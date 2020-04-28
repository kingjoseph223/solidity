/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
/**
 * Class that contains contextual information during IR generation.
 */

#include <libsolidity/codegen/ir/IRGenerationContext.h>

#include <libsolidity/codegen/YulUtilFunctions.h>
#include <libsolidity/codegen/ABIFunctions.h>
#include <libsolidity/ast/AST.h>
#include <libsolidity/ast/TypeProvider.h>

#include <libsolutil/Whiskers.h>
#include <libsolutil/StringUtils.h>

using namespace std;
using namespace solidity;
using namespace solidity::util;
using namespace solidity::frontend;

string IRGenerationContext::enqueueFunctionForCodeGeneration(FunctionDefinition const& _function)
{
	string name = functionName(_function);

	if (!m_functions.contains(name))
		m_functionGenerationQueue.insert(&_function);

	return name;
}

FunctionDefinition const* IRGenerationContext::dequeueFunctionForCodeGeneration()
{
	solAssert(!m_functionGenerationQueue.empty(), "");

	FunctionDefinition const* result = *m_functionGenerationQueue.begin();
	m_functionGenerationQueue.erase(m_functionGenerationQueue.begin());
	return result;
}

ContractDefinition const& IRGenerationContext::mostDerivedContract() const
{
	solAssert(m_mostDerivedContract, "Most derived contract requested but not set.");
	return *m_mostDerivedContract;
}

IRVariable const& IRGenerationContext::addLocalVariable(VariableDeclaration const& _varDecl)
{
	auto const& [it, didInsert] = m_localVariables.emplace(
		std::make_pair(&_varDecl, IRVariable{_varDecl})
	);
	solAssert(didInsert, "Local variable added multiple times.");
	return it->second;
}

IRVariable const& IRGenerationContext::localVariable(VariableDeclaration const& _varDecl)
{
	solAssert(
		m_localVariables.count(&_varDecl),
		"Unknown variable: " + _varDecl.name()
	);
	return m_localVariables.at(&_varDecl);
}

void IRGenerationContext::addStateVariable(
	VariableDeclaration const& _declaration,
	u256 _storageOffset,
	unsigned _byteOffset
)
{
	m_stateVariables[&_declaration] = make_pair(move(_storageOffset), _byteOffset);
}

string IRGenerationContext::functionName(FunctionDefinition const& _function)
{
	// @TODO previously, we had to distinguish creation context and runtime context,
	// but since we do not work with jump positions anymore, this should not be a problem, right?
	return "fun_" + _function.name() + "_" + to_string(_function.id());
}

string IRGenerationContext::functionName(VariableDeclaration const& _varDecl)
{
	return "getter_fun_" + _varDecl.name() + "_" + to_string(_varDecl.id());
}

string IRGenerationContext::creationObjectName(ContractDefinition const& _contract) const
{
	return _contract.name() + "_" + toString(_contract.id());
}
string IRGenerationContext::runtimeObjectName(ContractDefinition const& _contract) const
{
	return _contract.name() + "_" + toString(_contract.id()) + "_deployed";
}

string IRGenerationContext::newYulVariable()
{
	return "_" + to_string(++m_varCounter);
}

string IRGenerationContext::trySuccessConditionVariable(Expression const& _expression) const
{
	// NB: The TypeChecker already ensured that the Expression is of type FunctionCall.
	solAssert(
		static_cast<FunctionCallAnnotation const&>(_expression.annotation()).tryCall,
		"Parameter must be a FunctionCall with tryCall-annotation set."
	);

	return "trySuccessCondition_" + to_string(_expression.id());
}

map<Arity, set<FunctionDefinition const*>> IRGenerationContext::consumeInternalDispatchMap()
{
	map<Arity, set<FunctionDefinition const*>> result = move(m_internalDispatchMap);

	m_internalDispatchTargetCandidates.clear();
	m_internalDispatchMap.clear();

	solAssert(
		all_of(result.begin(), result.end(), [](auto const& pair){ return !pair.second.empty(); }),
		"Internal dispatch function registered even though no functions of the corresponding arity to be dispatched were found"
	);

	return result;
}

string IRGenerationContext::registerInternalDispatchTargetCandidate(FunctionDefinition const& _function)
{
	Arity arity = functionArity(_function);
	solAssert(m_internalDispatchMap.count(arity) == 0 || m_internalDispatchTargetCandidates.count(arity) == 0, "");

	if (m_internalDispatchMap.count(arity) == 0)
	{
		// We have not had the need to generate a dispatch for this arity yet.
		// Store the candidate but do not generate code for it just yet.
		m_internalDispatchTargetCandidates.try_emplace(arity, set<FunctionDefinition const*>{});
		m_internalDispatchTargetCandidates[arity].insert(&_function);
	}
	else
	{
		// Dispatch for this arity will be generated so we know we need to generate the function too.
		m_internalDispatchMap[arity].insert(&_function);
		enqueueFunctionForCodeGeneration(_function);
	}

	return internalDispatchFunctionName(arity);
}

string IRGenerationContext::registerInternalDispatch(Arity const& _arity)
{
	solAssert(m_internalDispatchMap.count(_arity) == 0 || m_internalDispatchTargetCandidates.count(_arity) == 0, "");

	if (m_internalDispatchMap.count(_arity) == 0)
	{
		if (m_internalDispatchTargetCandidates.count(_arity) > 0)
		{
			auto pairIt = m_internalDispatchTargetCandidates.find(_arity);
			m_internalDispatchMap[_arity] = move(pairIt->second);
			m_internalDispatchTargetCandidates.erase(pairIt);
		}

		// We were holding off with adding these candidates to the queue but now we know we need them
		for (auto const* function: m_internalDispatchMap[_arity])
			enqueueFunctionForCodeGeneration(*function);
	}

	return internalDispatchFunctionName(_arity);
}

Arity IRGenerationContext::functionArity(FunctionDefinition const& _function)
{
	FunctionType const* functionType = TypeProvider::function(_function)->asCallableFunction(false);
	solAssert(functionType, "");
	return functionArity(*functionType);
}

Arity IRGenerationContext::functionArity(FunctionType const& _functionType)
{
	return {
		TupleType(_functionType.parameterTypes()).sizeOnStack(),
		TupleType(_functionType.returnParameterTypes()).sizeOnStack()
	};
}

string IRGenerationContext::internalDispatchFunctionName(Arity const& _arity)
{
	return "dispatch_internal"
		"_in_" + to_string(_arity.in) +
		"_out_" + to_string(_arity.out);
}

string IRGenerationContext::internalDispatch(set<FunctionDefinition const*> const& _functions)
{
	solAssert(!_functions.empty(), "");

	Arity arity = functionArity(**_functions.begin());

	vector<map<string, string>> cases;
	for (auto const* function: _functions)
	{
		solAssert(function, "");
		solAssert(functionArity(*function) == arity, "One dispatch function can only handle functions of the same arity");
		solAssert(!function->isConstructor(), "");
		// 0 is reserved for uninitialized function pointers
		solAssert(function->id() != 0, "Unexpected function ID: 0");

		cases.emplace_back(map<string, string>{
			{"funID", to_string(function->id())},
			{"name", functionName(*function)}
		});
	}

	string funName = internalDispatchFunctionName(arity);
	return m_functions.createFunction(funName, [&, cases(move(cases))]() {
		Whiskers templ(R"(
			function <functionName>(fun <comma> <in>) <arrow> <out> {
				switch fun
				<#cases>
				case <funID>
				{
					<out> <assignment_op> <name>(<in>)
				}
				</cases>
				default { invalid() }
			}
		)");
		templ("functionName", funName);
		templ("comma", arity.in> 0 ? "," : "");
		YulUtilFunctions utils(m_evmVersion, m_revertStrings, m_functions);
		templ("in", suffixedVariableNameList("in_", 0, arity.in));
		templ("arrow", arity.out> 0 ? "->" : "");
		templ("assignment_op", arity.out> 0 ? ":=" : "");
		templ("out", suffixedVariableNameList("out_", 0, arity.out));
		templ("cases", move(cases));
		return templ.render();
	});
}

YulUtilFunctions IRGenerationContext::utils()
{
	return YulUtilFunctions(m_evmVersion, m_revertStrings, m_functions);
}

ABIFunctions IRGenerationContext::abiFunctions()
{
	return ABIFunctions(m_evmVersion, m_revertStrings, m_functions);
}

std::string IRGenerationContext::revertReasonIfDebug(std::string const& _message)
{
	return YulUtilFunctions::revertReasonIfDebug(m_revertStrings, _message);
}

