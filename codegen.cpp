#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/JIT.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/PassManager.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include <cstdio>
#include <map>
#include <string>
#include <vector>
namespace project473 {
extern "C" {
  #include "ast.h"
}
}

using namespace llvm;

extern "C" int initLex(int argc, char** argv);
extern "C" void initSymbolTable();  
extern "C" int  yyparse();
extern "C" int typecheck();
extern "C" int gettoken();
extern "C" void print_Ast();
extern "C" void printSymbolTable(int flag); 
extern "C" project473::AstNodePtr program;
extern "C" project473::SymbolTableStackEntryPtr symbolStackTop;
project473::Type* fun_ret_type;

static Module *TheModule;
static IRBuilder<> Builder(getGlobalContext());
static std::map<std::string, AllocaInst*> NamedValues;
static std::map<std::string, Function*> Functions;
//BasicBlock *ReturnBB=0;
Function *TheFunction=0;
BasicBlock *ReturnBB = 0;
AllocaInst *RetAlloca=0;
int return_scope;
bool print=false;
void Error(const char *Str) { fprintf(stderr, "Error: %s\n", Str);}
Value *ErrorV(const char *Str) { Error(Str); return 0; }

/// CreateEntryBlockAlloca - Create an alloca instruction in the entry block of
/// the function.  VarName is an std::string containing the variable name
static AllocaInst *CreateEntryBlockAlloca(Function *TheFunction, const std::string &VarName) {

	//IRBuilder<> TmpB(TheFunction->getEntryBlock(),TheFunction->getEntryBlock().begin());
  	//return TmpB.CreateAlloca(Type::getInt32Ty(getGlobalContext()), 0, VarName);
  
}

/// CreateEntryBlockArrayAlloca - Create an alloca instruction for an array in the entry block of
/// the function.  VarName is an std::string containing the array name, arraySize is the number of elements in the array
static AllocaInst *CreateEntryBlockArrayAlloca(Function *TheFunction, const std::string &VarName, int arraySize) {

}

///Codegen the Allocas for local variables that correspond to the formal variables of function F.
///function_node is an AST node representing a function. Steps
///1. For every formal variable, get its name from the AST, create a Type object
// and call AllocaInst* alloca_inst = Builder.CreateAlloca(Type, name);
//2. set NamedValues[name] = alloca_inst
//3. For every formal variable of the function, create a store instruction that copies the value
//from the formal variable to the allocated local variable.
void createFormalVarAllocations(Function *F, project473::AstNodePtr function_node) {
	if(print)
	printf("\n Inside createFormalVarAllocations() method");
	project473::AstNodePtr formalVarNode=function_node->children[0];
	AllocaInst* alloca_inst=0;
	Value* Val=0;
	for(Function::arg_iterator I = F->arg_begin(), E = F->arg_end(); I != E; ++I){
		if(print)
			printf("\n Exists some formal variables!!");
		char* name = strdup(formalVarNode->nSymbolPtr->id); 
		if(print)
		printf("\n Formal var creating now is %s",name);
  		std::string Name(name);
		project473::Type* type = formalVarNode->nSymbolPtr->stype;
		if(type->kind==project473::INT){
			//Val = Codegen_Expression(formalVarNode);
			alloca_inst = Builder.CreateAlloca(Builder.getInt32Ty(),0, Name);
			Builder.CreateStore(I, alloca_inst);
		}
		else if(type->kind==project473::ARRAY){
			//Val = Codegen_Expression(formalVarNode);
			alloca_inst = Builder.CreateAlloca(llvm::ArrayType::get(Builder.getInt32Ty(), type->dimension),0, Name);
			Builder.CreateStore(I, alloca_inst);
		}
		NamedValues[Name] = alloca_inst;
		formalVarNode=formalVarNode->sibling;
		
	}

}

Function* Codegen_Function_Declaration(project473::AstNodePtr declaration_node) {
  char* fname = strdup(declaration_node->nSymbolPtr->id); 
  std::string Name(fname);
  std::vector<Type*> formalvars;
  project473::AstNodePtr formalVar = declaration_node->children[0]; 
  while(formalVar) { 
    if(formalVar->nSymbolPtr->stype->kind == project473::INT) {
      formalvars.push_back(Type::getInt32Ty(getGlobalContext()));
      formalVar=formalVar->sibling;
    }
    else {
      printf("Error, formal variable is not an int, in line: %d", formalVar->nLinenumber);
    }
  }
  project473::Type* functionTypeList = declaration_node->nSymbolPtr->stype->function;
  FunctionType *FT;
  if(functionTypeList->kind==project473::INT) { 
     FT = FunctionType::get(Type::getInt32Ty(getGlobalContext()), formalvars, false);
  }
  else if(functionTypeList->kind==project473::VOID) {
    FT = FunctionType::get(Type::getVoidTy(getGlobalContext()), formalvars, false);
  }

  Function *F = Function::Create(FT, Function::ExternalLinkage, Name, TheModule);
  // Set names for all arguments. Reuse formalVar
  formalVar = declaration_node->children[0];
  for (Function::arg_iterator AI = F->arg_begin(); formalVar != NULL; ++AI, formalVar=formalVar->sibling) {
          std::string argName(formalVar->nSymbolPtr->id);
          AI->setName(argName);
  }
  Functions[Name] = F; //add the Function to the map of functions
  return F;
}

///Generate code for expressions
Value* Codegen_Expression(project473::AstNodePtr expression) {
	Value* L=0;
	Value* R=0;
	if(expression->eKind==project473::GT_EXP||expression->eKind==project473::LT_EXP||expression->eKind==project473::GE_EXP||expression->eKind==project473::LE_EXP||expression->eKind==project473::EQ_EXP||expression->eKind==project473::NE_EXP||expression->eKind==project473::ADD_EXP||expression->eKind==project473::SUB_EXP||expression->eKind==project473::MULT_EXP||expression->eKind==project473::DIV_EXP){
		if(print)
		printf("\n INSIDE A BINARY EXPRESSION");
		if(expression->children[0]->eKind==project473::VAR_EXP||expression->children[0]->eKind==project473::ARRAY_EXP){
			//Value* LAllocated = Codegen_Expression(expression->children[0]);
			 L = Builder.CreateLoad(Codegen_Expression(expression->children[0]), "leftoperand");
		}
		else if(expression->children[0]->eKind==project473::CONST_EXP){
			//L = Builder.CreateLoad(Codegen_Expression(expression->children[0]), "leftoperand");
			L=0;
		}
		if(expression->children[1]->eKind==project473::VAR_EXP||expression->children[1]->eKind==project473::ARRAY_EXP){
			//Value* RAllocated = Codegen_Expression(expression->children[1]);
			R = Builder.CreateLoad(Codegen_Expression(expression->children[1]), "secondoperand");
		}
		else if(expression->children[1]->eKind==project473::CONST_EXP){
			//R = Builder.CreateLoad(Codegen_Expression(expression->children[1]), "secondoperand");
			R=0;
		}
	}

    if(expression->eKind==project473::ASSI_EXP) {
		if(print)
		printf("\n Inside ASSI_EXP");
		Value* RAllocated =0;
		Value* LAllocated = Codegen_Expression(expression->children[0]);
		if(expression->children[1]->eKind==project473::CONST_EXP){
			Builder.CreateStore(Codegen_Expression(expression->children[1]), LAllocated);
		}
		else if(expression->children[1]->eKind==project473::VAR_EXP||expression->children[1]->eKind==project473::ARRAY_EXP){
			RAllocated = Codegen_Expression(expression->children[1]);
			R = Builder.CreateLoad(RAllocated, "secondoperand");
			Builder.CreateStore(R, LAllocated);
		}
		else{
			Builder.CreateStore(Codegen_Expression(expression->children[1]), LAllocated);
		}
		if(print)
		printf("\n Before return in Assi_Exp");
		return NULL;
    }
    else if(expression->eKind==project473::VAR_EXP) {
		if(print)
		printf("\n Inside VAR_EXP");
		char* name = strdup(expression->nSymbolPtr->id); 
		if(print)
		printf("\n VAriable name assigning is %s",name);
	  	std::string varName(name);
	  	if(NamedValues[varName]!=NULL){
			AllocaInst* pointerToLocal = NamedValues[varName];
			if(print)
			printf("\n VAriable is available in NamedValues[] and returning ");
			return pointerToLocal;
		}
		else{
			if(print)
			printf("\n Variable is available in global scope and returning from there,,!!");
			llvm::GlobalVariable* gVar = TheModule->getNamedGlobal(varName);
			return gVar;
		}
    }
    else if(expression->eKind==project473::CONST_EXP) {  
		if(print)
		printf("\n Inside CONST_EXP");   
		return Builder.getInt32(expression->nValue);
    }
    else if(expression->eKind==project473::GT_EXP) {
		if(print)
		printf("\n Inside GT_EXP");
		if(L==NULL && R==NULL){
			return Builder.CreateICmpUGT(Codegen_Expression(expression->children[0]),Codegen_Expression(expression->children[1]),"gt");
		}
		if(L==NULL && R!=NULL){
			return Builder.CreateICmpUGT(Codegen_Expression(expression->children[0]),R,"gt");
		}
		if(L!=NULL && R==NULL){
			return Builder.CreateICmpUGT(L,Codegen_Expression(expression->children[1]),"gt");
		}
		else
        return Builder.CreateICmpUGT(L,R,"gt");
    }
    else if(expression->eKind==project473::LT_EXP) {
		if(print)
		printf("\n Inside LT_EXP");
		if(L==NULL && R==NULL){
			return Builder.CreateICmpULT(Codegen_Expression(expression->children[0]),Codegen_Expression(expression->children[1]),"lt");
		}
		if(L==NULL && R!=NULL){
			return Builder.CreateICmpULT(Codegen_Expression(expression->children[0]),R,"lt");
		}
		if(L!=NULL && R==NULL){
			return Builder.CreateICmpULT(L,Codegen_Expression(expression->children[1]),"lt");
		}
		else
			return Builder.CreateICmpULT(L,R,"lt");
    }
    else if(expression->eKind==project473::GE_EXP) {
		if(print)
		printf("\n Inside GE_EXP");
		if(L==NULL && R==NULL){
			return Builder.CreateICmpUGE(Codegen_Expression(expression->children[0]),Codegen_Expression(expression->children[1]),"ge");
		}
		if(L==NULL && R!=NULL){
			return Builder.CreateICmpUGE(Codegen_Expression(expression->children[0]),R,"ge");
		}
		if(L!=NULL && R==NULL){
			return Builder.CreateICmpUGE(L,Codegen_Expression(expression->children[1]),"ge");
		}
		else
     	return Builder.CreateICmpUGE(L,R,"ge");  
    }
    else if(expression->eKind==project473::LE_EXP) {
		if(print)
		printf("\n Inside LE_EXP");
		if(L==NULL && R==NULL){
			return Builder.CreateICmpULE(Codegen_Expression(expression->children[0]),Codegen_Expression(expression->children[1]),"le");
		}
		if(L==NULL && R!=NULL){
			return Builder.CreateICmpULE(Codegen_Expression(expression->children[0]),R,"le");
		}
		if(L!=NULL && R==NULL){
			return Builder.CreateICmpULE(L,Codegen_Expression(expression->children[1]),"le");
		}
		else
        return Builder.CreateICmpULE(L,R,"le");
    }
    else if(expression->eKind==project473::EQ_EXP) {
		if(print)
		printf("\n Inside EQ_EXP");
		if(L==NULL && R==NULL){
			return Builder.CreateICmpEQ(Codegen_Expression(expression->children[0]),Codegen_Expression(expression->children[1]),"eq");
		}
		if(L==NULL && R!=NULL){
			return Builder.CreateICmpEQ(Codegen_Expression(expression->children[0]),R,"eq");
		}
		if(L!=NULL && R==NULL){
			return Builder.CreateICmpEQ(L,Codegen_Expression(expression->children[1]),"eq");
		}
		else
       return Builder.CreateICmpEQ(L,R,"eq");
    }
    else if(expression->eKind==project473::NE_EXP) {
		if(print)
		printf("\n Inside NT_EXP");
		if(L==NULL && R==NULL){
			return Builder.CreateICmpNE(Codegen_Expression(expression->children[0]),Codegen_Expression(expression->children[1]),"ne");
		}
		if(L==NULL && R!=NULL){
			return Builder.CreateICmpNE(Codegen_Expression(expression->children[0]),R,"ne");
		}
		if(L!=NULL && R==NULL){
			return Builder.CreateICmpNE(L,Codegen_Expression(expression->children[1]),"ne");
		}
		else
       return Builder.CreateICmpNE(L,R,"ne");
    }
    else if(expression->eKind==project473::ADD_EXP) {
		if(print)
		printf("\n Inside ADD_EXP");
		if(L==NULL && R==NULL){
			return Builder.CreateAdd(Codegen_Expression(expression->children[0]),Codegen_Expression(expression->children[1]),"add",false,false);
		}
		if(L==NULL && R!=NULL){
			return Builder.CreateAdd(Codegen_Expression(expression->children[0]),R,"add",false,false);
		}
		if(L!=NULL && R==NULL){
			return Builder.CreateAdd(L,Codegen_Expression(expression->children[1]),"add",false,false);
		}
		else
			return Builder.CreateAdd(L,R,"add",false,false);
    }
    else if(expression->eKind==project473::SUB_EXP) {
		if(print)
		printf("\n Inside SUB_EXP");
		if(L==NULL && R==NULL){
			return Builder.CreateSub(Codegen_Expression(expression->children[0]),Codegen_Expression(expression->children[1]),"sub",false,false);
		}
		if(L==NULL && R!=NULL){
			return Builder.CreateSub(Codegen_Expression(expression->children[0]),R,"sub",false,false);
		}
		if(L!=NULL && R==NULL){
			return Builder.CreateSub(L,Codegen_Expression(expression->children[1]),"sub",false,false);
		}
		else
        return Builder.CreateSub(L,R,"sub",false,false);
    }
    else if(expression->eKind==project473::MULT_EXP) {
		if(print)
		printf("\n Inside MUL_EXP");
		if(L==NULL && R==NULL){
			return Builder.CreateMul(Codegen_Expression(expression->children[0]),Codegen_Expression(expression->children[1]),"mul",false,false);
		}
		if(L==NULL && R!=NULL){
			return Builder.CreateMul(Codegen_Expression(expression->children[0]),R,"mul",false,false);
		}
		if(L!=NULL && R==NULL){
			return Builder.CreateMul(L,Codegen_Expression(expression->children[1]),"mul",false,false);
		}
		else
        return Builder.CreateMul(L,R,"mul",false,false);
    }
    else if(expression->eKind==project473::DIV_EXP) {
		if(print)
		printf("\n Inside DIV_EXP");
		if(L==NULL && R==NULL){
			return Builder.CreateUDiv(Codegen_Expression(expression->children[0]),Codegen_Expression(expression->children[1]),"div",false);
		}
		if(L==NULL && R!=NULL){
			return Builder.CreateUDiv(Codegen_Expression(expression->children[0]),R,"div",false);
		}
		if(L!=NULL && R==NULL){
			return Builder.CreateUDiv(L,Codegen_Expression(expression->children[1]),"div",false);
		}
		else
        return Builder.CreateUDiv(L,R,"div",false);
    }
    else if(expression->eKind==project473::ARRAY_EXP) {
		if(print)
		printf("\n Inside ARRAY_EXP");
	    Value* indexVal = Codegen_Expression(expression->children[0]);
		llvm::Value *Zero = Builder.getInt32(0);
		llvm::Value *Args[] = { Zero, indexVal };
		char* name = strdup(expression->nSymbolPtr->id);
		if(print)
		printf("\n Array name is %s",expression->nSymbolPtr->id); 
	  	std::string Name(name);
		Value* arr_name = NamedValues[Name];
		if(arr_name==NULL){
			if(print)
			printf("\n arr_name allocation is NULL");
		}
		else
			if(print)
			printf("\n arr_name allocation is NOT NULL");
		Value* pointerElement = Builder.CreateInBoundsGEP(arr_name, Args, "arrayidx");
		if(print)
		printf("\n before returning from ARRAY_EXP");
		return pointerElement;
    }
    else if(expression->eKind==project473::CALL_EXP) { 
		if(print)
		printf("\n Inside CALL_EXP");
		std::string Callee(expression->fname);
		Function *CalleeF = TheModule->getFunction(Callee); //alternatively Functions[Callee] can be used here
		std::vector<Value*> ArgsV;
		project473::AstNodePtr currentArg = expression->children[0]; //this is the list of arguments
		while(currentArg != NULL) {
			if(print)
			printf("\n Entered in while of CALL_EXP");
		Value* arg = Codegen_Expression(currentArg);
		if(currentArg->eKind==project473::VAR_EXP||currentArg->eKind==project473::ARRAY_EXP) { //the codedegen for these two returns the AllocaInst*-s of NamedValues, must do a load before
		arg=Builder.CreateLoad(arg,"arg");
		}
		ArgsV.push_back(arg); //push the value into the vector of arguments
		currentArg = currentArg->sibling;
		}
		if(print)
			printf("\n before returning in CALL_EXP");
		if(ArgsV.empty())
				return Builder.CreateCall(CalleeF);
			return Builder.CreateCall(CalleeF, ArgsV, "call");
		
    }
  return 0;
}

///Generates code for the statements.
//Calls Codegen_Expression
Value* Codegen_Statement(project473::AstNodePtr statement) {
	if(!statement)
		return NULL;
	if(print)
	printf("Inside a statement %d\n",statement->sKind);
    if(statement->sKind==project473::EXPRESSION_STMT) {
		if(print)
		printf("\n Inside EXPRESSION_STMT");
         return Codegen_Expression(statement->children[0]);
    }
    else if(statement->sKind==project473::RETURN_STMT) {
		if(print)
		printf("\n Inside RETURN_STMT");
		if(fun_ret_type->kind==project473::VOID){
			if(return_scope==0){
				Builder.CreateRetVoid();
				return NULL;
			}
			else{
				ReturnBB=BasicBlock::Create(getGlobalContext(), "return");
				Builder.CreateBr(ReturnBB);	
				TheFunction->getBasicBlockList().push_back(ReturnBB);
				Builder.CreateRetVoid();
				return NULL;
			}
		}
	else if(fun_ret_type->kind==project473::INT){
		if(return_scope==0){
			if(statement->children[0]!=NULL){
				if(statement->children[0]->eKind==project473::VAR_EXP||statement->children[0]->eKind==project473::ARRAY_EXP){
					Value* retReg=0;
					Value* val=Codegen_Expression(statement->children[0]);
					//AllocaInst* retvalalloca = Builder.CreateAlloca(Builder.getInt32Ty(),0, "retval");
					//Builder.CreateStore(val,retvalalloca);
					retReg=Builder.CreateLoad(val,"retregister");
					//Builder.CreateStore(retReg,retvalalloca);
					Builder.CreateRet(retReg);
					return NULL;
				}
				else{
					Value* val=Codegen_Expression(statement->children[0]); 
					Builder.CreateRet(val);
					return NULL;
				}
			}
		}
		else{
			ReturnBB=BasicBlock::Create(getGlobalContext(), "return");
			Value* retReg=0;
			if(statement->children[0]!=NULL){
				if(statement->children[0]->eKind==project473::CONST_EXP){
					AllocaInst* retvalalloca = Builder.CreateAlloca(Builder.getInt32Ty(),0, "retval");
					Value* val=Codegen_Expression(statement->children[0]);
					Builder.CreateStore(Codegen_Expression(statement->children[0]),retvalalloca);
					retReg=Builder.CreateLoad(retvalalloca,"retregister");
				}
				else if(statement->children[0]->eKind==project473::VAR_EXP||statement->children[0]->eKind==project473::ARRAY_EXP){
						
						Value* val=Codegen_Expression(statement->children[0]); 
						AllocaInst* retvalalloca = Builder.CreateAlloca(Builder.getInt32Ty(),0, "retval");
						Builder.CreateStore(val,retvalalloca);
						retReg=Builder.CreateLoad(retvalalloca,"retregister");
						//Builder.CreateStore(retReg,retvalalloca);
						Builder.CreateRet(retReg);
				}
				else{
				Value* val=Codegen_Expression(statement->children[0]); 
				AllocaInst* retvalalloca = Builder.CreateAlloca(Builder.getInt32Ty(),0, "retval");
				Builder.CreateStore(val,retvalalloca);
				retReg=Builder.CreateLoad(retvalalloca,"retregister");
				}
			Builder.CreateBr(ReturnBB);	
			TheFunction->getBasicBlockList().push_back(ReturnBB);
			Builder.CreateRet(retReg);
			return NULL;
		}
	}
          
    }
} 
    else if(statement->sKind==project473::IF_THEN_ELSE_STMT) { 
		if(print)
		printf("\n Inside IF_THEN_ELSE_STMT");
		if(statement->children[2]!=NULL){
			return_scope++;
			Value* condition = Codegen_Expression(statement->children[0]);
			BasicBlock *ThenBB = BasicBlock::Create(getGlobalContext(), "if.t", TheFunction);
			BasicBlock *ElseBB = BasicBlock::Create(getGlobalContext(), "if.e");
			BasicBlock *MergeBB = BasicBlock::Create(getGlobalContext(), "if.end");
			Builder.CreateCondBr(condition, ThenBB, ElseBB);
			Builder.SetInsertPoint(ThenBB);
			Value *ThenV = Codegen_Statement(statement->children[1]); //generate code for the then part
			Builder.CreateBr(MergeBB); //after generating code, create a branch to the Merge basic block
			ThenBB = Builder.GetInsertBlock();
			TheFunction->getBasicBlockList().push_back(ElseBB); //add the Else basic block to the list of basic blocks of the function
			Builder.SetInsertPoint(ElseBB);
			Value *ElseV = Codegen_Statement(statement->children[2]);
			Builder.CreateBr(MergeBB); //after generating code, create a branch to the Merge basic block
			TheFunction->getBasicBlockList().push_back(MergeBB);//add the Merge basic block to the list of basic blocks of the function
			Builder.SetInsertPoint(MergeBB);
			return_scope--;
			return NULL;
		}
		else{
			return_scope++;
			Value* condition = Codegen_Expression(statement->children[0]);
			BasicBlock *ThenBB = BasicBlock::Create(getGlobalContext(), "if.t", TheFunction);
			BasicBlock *MergeBB = BasicBlock::Create(getGlobalContext(), "if.end");
			Builder.CreateCondBr(condition, ThenBB, MergeBB);
			Builder.SetInsertPoint(ThenBB);
			Value *ThenV = Codegen_Statement(statement->children[1]);
			Builder.CreateBr(MergeBB);
			ThenBB = Builder.GetInsertBlock();
			TheFunction->getBasicBlockList().push_back(MergeBB);
			Builder.SetInsertPoint(MergeBB);
			return_scope--;	
			return NULL;
		}
	
    }
    else if(statement->sKind==project473::COMPOUND_STMT) {
		if(print)
		printf("\n Inside COMPOUND_STMT");
		project473::AstNodePtr comp_stmt=statement;
		comp_stmt=comp_stmt->children[0];
		Value* val;
		while(comp_stmt){
			val=Codegen_Statement(comp_stmt);
			comp_stmt=comp_stmt->sibling;
		}
    }
    else if(statement->sKind==project473::WHILE_STMT) {
		if(print)
		printf("\n Inside WHILE_STMT");
				return_scope++;
				BasicBlock *WhileCond = BasicBlock::Create(getGlobalContext(), "while.cond", TheFunction);
				Builder.CreateBr(WhileCond); 
				Builder.SetInsertPoint(WhileCond);
				Value* condition = Codegen_Expression(statement->children[0]);
	            BasicBlock *WhileBody = BasicBlock::Create(getGlobalContext(), "while.body");
	            BasicBlock *MergeBlock = BasicBlock::Create(getGlobalContext(), "Merge.block");
	            Builder.CreateCondBr(condition, WhileBody , MergeBlock);
	            TheFunction->getBasicBlockList().push_back(WhileBody);
	            Builder.SetInsertPoint(WhileBody);
				Value *WhileBodyV = Codegen_Statement(statement->children[1]); //generate code for the body part
				Builder.CreateBr(WhileCond); //after generating code, create a branch to the condition basic block
				//WhileBody = Builder.GetInsertBlock();
				//Builder.CreateBr(MergeBlock); //after generating code, create a branch to the Merge basic block
				TheFunction->getBasicBlockList().push_back(MergeBlock);//add the Merge basic block to the list of basic blocks of the function
				Builder.SetInsertPoint(MergeBlock);
				return_scope--;
				return NULL;
    }
    return 0; 
}

//generates the code for the body of the function. Steps
//1. Generate alloca instructions for the local variables
//2. Iterate over list of statements and call Codegen_Statement for each of them
Value* Codegen_Function_Body(project473::AstNodePtr function_body) {
			if(print)
			printf("\n Inside Codegen_Function_Body() function");
			return_scope=0;
		project473::SymbolTablePtr hashTab = function_body->children[1]->nSymbolTabPtr;
		project473::Type* type=0;
		AllocaInst* alloca_inst=0;
		for(int i=0;i<MAXHASHSIZE;i++){
			//printf("\n Inside FOR ");
			if(hashTab!=NULL && hashTab->hashTable[i]!=NULL){
				//printf("\n Inside hashtable check to NULL ");
				char* name = strdup(hashTab->hashTable[i]->id); 
				std::string Name(name);
				if(print)
				printf("\n After dup name ");
				type = hashTab->hashTable[i]->stype;
				if (type->kind==project473::INT) {
					if(print)
					printf("\n Int type allocation ");
					llvm::IntegerType *intType = Builder.getInt32Ty();
					alloca_inst=Builder.CreateAlloca(intType,0, Name);
			    }
			    else if(type->kind==project473::ARRAY) {
					if(print)
					printf("\n Array type allocation for array %s",name);
					llvm::ArrayType* arrType = llvm::ArrayType::get(Type::getInt32Ty(getGlobalContext()), type->dimension);
					alloca_inst=Builder.CreateAlloca(arrType,0, Name);
			    }
			    NamedValues[Name]=alloca_inst;
		}
	}
	createFormalVarAllocations(TheFunction,function_body);
		if(print)
		printf("\n After WHILE of Codegen_Function_Body() function");
	project473::AstNodePtr  function_body_iterator=function_body->children[1];
	Value* val=0;
		val=Codegen_Statement(function_body_iterator);
	return NULL;
}

//generates code for the function, verifies the code for the function. Steps:
//1. Create the entry block, place the insert point for the builder in the entry block
//2. Call CreateFormalVarAllocations
//3. Call Codegen_Function_Body
//4. Insert 'return' basic block if needed
Function* Codegen_Function(project473::AstNodePtr function_node) {
	if(print)
	printf("\n Indise codegen_function()");
	fun_ret_type = function_node->nSymbolPtr->stype->function;
	char* fname = strdup(function_node->nSymbolPtr->id); 
  	std::string Name(fname);
	TheFunction = Functions[Name];
	if(print){
	printf("\nTheFunction refers to %s",fname);
	printf("\n AFTER Functions[Name]");
	}
	BasicBlock *BB = BasicBlock::Create(getGlobalContext(), "entry" , TheFunction);
	Builder.SetInsertPoint(BB);
	if(print)
	printf("\n before createFormalVarAllocations() call");
	//createFormalVarAllocations(TheFunction,function_node);
	if(print)
	printf("\n after createFormalVarAllocations() call");
	if(print)
	printf("\n before Codegen_Function_Body() call");
	Codegen_Function_Body(function_node);
	if(print)
	printf("\n after Codegen_Function_Body() call");
	return TheFunction;
	//TheFunction->getBasicBlockList().push_back(ReturnBB);
}

void initializeFunctions(project473::AstNodePtr program) {
    project473::AstNodePtr currentFun = program;
    while(currentFun != NULL) {
       Function *TheFunction = Codegen_Function_Declaration(currentFun);
       currentFun=currentFun->sibling;
    }
}

void codegen() {
	InitializeNativeTarget();
	LLVMContext &Context = getGlobalContext();
	// Make the module, which holds all the code.
	TheModule = new Module("codefile", Context);
	//Codegen the global variables
	//project473::ElementPtr currentGlobal = symbolStackTop->symbolTablePtr->queue;
	/*while(currentGlobal != NULL) {
		printf("Here\n");
		printf("\n cur global symbol is %s",currentGlobal->id);
		printf("\n AFTER PRINT");
		printf("\n AFTER PRINT");
		if (currentGlobal->stype->kind==project473::INT) {
			
			char* VarName = strdup(currentGlobal->id);
			std::string globalVarName(VarName);
			llvm::IntegerType *type = Builder.getInt32Ty();
			TheModule->getOrInsertGlobal(globalVarName,type);
			llvm::GlobalVariable* gVar = TheModule->getNamedGlobal(globalVarName);
			gVar->setLinkage(llvm::GlobalValue::CommonLinkage);
	    }
	    else if(currentGlobal->stype->kind==project473::ARRAY) {
			
			IntegerType* type = Type::getInt32Ty(getGlobalContext()); //get base type of array, integer type
			int arraySize = currentGlobal->stype->dimension; //get array size
			llvm::ArrayType* arrType = llvm::ArrayType::get(type,arraySize); //create an array type of arraySize integers
			std::string globalVarName(currentGlobal->id); //get the name and transform it to std::string
			TheModule->getOrInsertGlobal(globalVarName,arrType); //insert a global array with that name in the module, when dumped out, 	the code will be generated automatically
			llvm::GlobalVariable* gVar = TheModule->getNamedGlobal(globalVarName); //get the object that represents the global variable 	in the module
			gVar->setLinkage(llvm::GlobalValue::CommonLinkage); //set linkage
			gVar->setInitializer(ConstantAggregateZero::get(arrType)); //set initializer to all zeros, this is the 'zeroinitializer'
	    }
	    printf("\n before NEXTING CURRENT GLOBALBEFORE");
		currentGlobal = currentGlobal->queue_next;
		printf("\n AFTER NEXTING CURRENT GLOBAL AFTER");
	}*/
	project473::SymbolTablePtr hashTab = symbolStackTop->symbolTablePtr;
	for(int i=0;i<MAXHASHSIZE;i++){
		if(hashTab->hashTable[i]!=NULL){
			if(print){
			printf("\n inside if of hash table check to null");
			printf("\n And id == %s ",hashTab->hashTable[i]->id);
			}
			if (hashTab->hashTable[i]->stype->kind==project473::INT) {
				char* VarName = strdup(hashTab->hashTable[i]->id);
				std::string globalVarName(VarName);
				llvm::IntegerType *type = Builder.getInt32Ty();
				TheModule->getOrInsertGlobal(globalVarName,type);
				llvm::GlobalVariable* gVar = TheModule->getNamedGlobal(globalVarName);
				gVar->setLinkage(llvm::GlobalValue::CommonLinkage);
		    }
		    else if(hashTab->hashTable[i]->stype->kind==project473::ARRAY) {
				IntegerType* type = Type::getInt32Ty(getGlobalContext()); //get base type of array, integer type
				int arraySize = hashTab->hashTable[i]->stype->dimension; //get array size
				llvm::ArrayType* arrType = llvm::ArrayType::get(type,arraySize); //create an array type of arraySize integers
				std::string globalVarName(hashTab->hashTable[i]->id); //get the name and transform it to std::string
				TheModule->getOrInsertGlobal(globalVarName,arrType); //insert a global array with that name in the module, when dumped out, 	the code will be generated automatically
				llvm::GlobalVariable* gVar = TheModule->getNamedGlobal(globalVarName); //get the object that represents the global variable 	in the module
				gVar->setLinkage(llvm::GlobalValue::CommonLinkage); //set linkage
				gVar->setInitializer(ConstantAggregateZero::get(arrType)); //set initializer to all zeros, this is the 'zeroinitializer'
		    }
		}
	}
	initializeFunctions(program);
	if(print)
	printf("\n After Initialize Functions");
	project473::AstNodePtr currentFunction = program;
	while(currentFunction != NULL) {
		if(print)
		printf("\n Inside WHILE before codegen_function()");
		Function* theFunction = Codegen_Function(currentFunction); 
		if(print)
		printf("\n Inside WHILE after codegen_function()");
		currentFunction = currentFunction->sibling; 
	}
  // Print out all of the generated code.
	std::string ErrInfo;
	llvm::raw_ostream* filestream = new llvm::raw_fd_ostream("./out.s",ErrInfo);
	TheModule->print(*filestream,0);
}

int main(int argc, char** argv) {
  initLex(argc,argv);
    initSymbolTable();  
    yyparse();
    int typ = typecheck();
    printf("\ntypecheck returned: %d\n", typ);
    codegen();
 return 0;
}
