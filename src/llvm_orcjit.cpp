#include "core.h"
#include "vm.h"
#include "heap.h"

/*
(current-environment (system-environment)) (native-compile)
*/
#include "llvm/ExecutionEngine/Orc/LLJIT.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"

using namespace std;
using namespace llvm;
using namespace llvm::orc;

ExitOnError ExitOnErr;

ThreadSafeModule createDemoModule() {
    auto Context = llvm::make_unique<LLVMContext>();
    auto M = llvm::make_unique<Module>("test", *Context);

    // Create the add1 function entry and insert this entry into module M.  The
    // function will have a return type of "int" and take an argument of "int".
    Function *Add1F =
        Function::Create(FunctionType::get(Type::getInt32Ty(*Context),
                                            {Type::getInt32Ty(*Context)}, false),
                        Function::ExternalLinkage, "add1", M.get());

    // Add a basic block to the function. As before, it automatically inserts
    // because of the last argument.
    BasicBlock *BB = BasicBlock::Create(*Context, "EntryBlock", Add1F);

    // Create a basic block builder with default parameters.  The builder will
    // automatically append instructions to the basic block `BB'.
    IRBuilder<> builder(BB);

    // Get pointers to the constant `1'.
    Value *One = builder.getInt32(1);

    // Get pointers to the integer argument of the add1 function...
    assert(Add1F->arg_begin() != Add1F->arg_end()); // Make sure there's an arg
    Argument *ArgX = &*Add1F->arg_begin();          // Get the arg
    ArgX->setName("AnArg"); // Give it a nice symbolic name for fun.

    // Create the add instruction, inserting it into the end of BB.
    Value *Add = builder.CreateAdd(One, ArgX);

    // Create the return instruction and add it to the basic block
    builder.CreateRet(Add);

    return ThreadSafeModule(std::move(M), std::move(Context));
}

int test_orcjit_pipeline() {

    int argc = 1;
    const char** argv;
    argv = (const char **)malloc(sizeof(char*));
    argv[0] = strdup("orc jit test");

    // Initialize LLVM.
    InitLLVM X(argc, argv);

    InitializeNativeTarget();
    InitializeNativeTargetAsmPrinter();

    cl::ParseCommandLineOptions(argc, argv, "HowToUseLLJIT");
    ExitOnErr.setBanner(std::string(argv[0]) + ": ");

    puts("Create an LLJIT instance.");
    auto J = ExitOnErr(LLJITBuilder().create());
    auto DL = J->getDataLayout();
    J->getMainJITDylib().setGenerator(
        ExitOnErr(orc::DynamicLibrarySearchGenerator::GetForCurrentProcess(DL.getGlobalPrefix())));

    auto M = createDemoModule();
    ExitOnErr(J->addIRModule(std::move(M)));

    J->getMainJITDylib().dump(llvm::outs());

    puts("Look up the JIT'd function, cast it to a function pointer, then call it.");
    auto Add1Sym = ExitOnErr(J->lookup("add1"));

    puts("got symbol");
    int (*Add1)(int) = (int (*)(int))Add1Sym.getAddress();

    int Result = Add1(42);
    outs() << "add1(42) = " << Result << "\n";

    return 0;
}

/*
(current-environment (system-environment)) (native-compile)
*/
