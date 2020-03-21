#define DECLEAR_COMMON_TYPES \
    auto IntptrTy = (sizeof(intptr_t) == 4 ? Type::getInt32Ty(C) : Type::getInt64Ty(C)); \
    auto IntptrPtrTy = sizeof(intptr_t) == 4 ? Type::getInt32PtrTy(C) : Type::getInt64PtrTy(C); \
    auto VoidTy = Type::getVoidTy(C);

#if INTPTR_MAX == INT32_MAX
    #define VALUE_INTPTR(_VAL_) IRB.getInt32((intptr_t)(_VAL_))
#elif INTPTR_MAX == INT64_MAX
    #define VALUE_INTPTR(_VAL_) IRB.getInt64((intptr_t)(_VAL_))
#else
    #error unsupported intptr_t size
#endif

#define DECLEAR_CONTEXT_VARS \
    LLVMContext& C = ctx.m_llvm_context; \
    IRBuilder<>& IRB = ctx.m_irb; \
    Module* M = ctx.m_module; \
    Function* F = ctx.m_function;

#define CREATE_LOAD_VM_REG(_VM_,_REG_) \
    (IRB.CreateLoad(IntptrTy, IRB.CreateGEP(_VM_, IRB.getInt32(offsetof(VM, _REG_) / sizeof(intptr_t)))))

#define CREATE_STORE_VM_REG(_VM_,_REG_,_VAL_) \
    (IRB.CreateStore(_VAL_, IRB.CreateGEP(_VM_, IRB.getInt32(offsetof(VM, _REG_) / sizeof(intptr_t)))))

#define CREATE_LOAD_CONT_REC(_CONT_,_REC_) \
    (IRB.CreateLoad(IntptrTy, IRB.CreateGEP(_CONT_, IRB.getInt32(offsetof(vm_cont_rec_t, _REC_) / sizeof(intptr_t)))))

#define CREATE_STORE_CONT_REC(_CONT_,_REC_,_VAL_) \
    (IRB.CreateStore(_VAL_, IRB.CreateGEP(_CONT_, IRB.getInt32(offsetof(vm_cont_rec_t, _REC_) / sizeof(intptr_t)))))

#define CREATE_LOAD_GLOC_REC(_GLOC_,_REC_) \
    (IRB.CreateLoad(IntptrTy, IRB.CreateGEP(_GLOC_, IRB.getInt32(offsetof(scm_gloc_rec_t, _REC_) / sizeof(intptr_t)))))

#define CREATE_LOAD_ENV_REC(_ENV_,_REC_) \
    (IRB.CreateLoad(IntptrTy, IRB.CreateGEP(_ENV_, IRB.getInt32(offsetof(vm_env_rec_t, _REC_) / sizeof(intptr_t)))))

#define CREATE_STORE_ENV_REC(_ENV_,_REC_,_VAL_) \
    (IRB.CreateStore(_VAL_, IRB.CreateGEP(_ENV_, IRB.getInt32(offsetof(vm_env_rec_t, _REC_) / sizeof(intptr_t)))))

#define CREATE_LEA_ENV_REC(_ENV_,_REC_) \
    (IRB.CreateBitOrPointerCast(IRB.CreateGEP(_ENV_, IRB.getInt32(offsetof(vm_env_rec_t, _REC_) / sizeof(intptr_t))), IntptrTy))

#define CREATE_LOAD_PAIR_REC(_PAIR_,_REC_) \
    (IRB.CreateLoad(IntptrTy, IRB.CreateGEP(_PAIR_, IRB.getInt32(offsetof(scm_pair_rec_t, _REC_) / sizeof(intptr_t)))))

#define CREATE_PUSH_VM_STACK(_VAL_) { \
            auto sp = CREATE_LOAD_VM_REG(vm, m_sp); \
            auto sp0 = IRB.CreateBitOrPointerCast(sp, IntptrPtrTy); \
            IRB.CreateStore(_VAL_, sp0); \
            CREATE_STORE_VM_REG(vm, m_sp, IRB.CreateAdd(sp, VALUE_INTPTR(sizeof(intptr_t)))); \
        }
#if USE_UNIFIED_STACK_CHECK
    #define CREATE_STACK_OVERFLOW_HANDLER(_BYTES_REQUIRED_) {}
#else
    #define CREATE_STACK_OVERFLOW_HANDLER(_BYTES_REQUIRED_) { \
                auto sp = CREATE_LOAD_VM_REG(vm, m_sp); \
                auto stack_limit = CREATE_LOAD_VM_REG(vm, m_stack_limit); \
                BasicBlock* stack_ok = BasicBlock::Create(C, "stack_ok", F); \
                BasicBlock* stack_overflow = BasicBlock::Create(C, "stack_overflow", F); \
                Value* stack_cond = IRB.CreateICmpULT(IRB.CreateAdd(sp, VALUE_INTPTR(_BYTES_REQUIRED_)), stack_limit); \
                IRB.CreateCondBr(stack_cond, stack_ok, stack_overflow); \
                IRB.SetInsertPoint(stack_overflow); \
                auto c_collect_stack = M->getOrInsertFunction("c_collect_stack", VoidTy, IntptrPtrTy, IntptrTy); \
                IRB.CreateCall(c_collect_stack, {vm, VALUE_INTPTR(_BYTES_REQUIRED_)}); \
                IRB.CreateBr(stack_ok); \
                IRB.SetInsertPoint(stack_ok); \
            }
#endif

#define CONS(a, d)      make_pair(vm->m_heap, (a), (d))
#define LIST1(e1)       CONS((e1), scm_nil)
#define LIST2(e1, e2)   CONS((e1), LIST1((e2)))
#define STACKP(p)       (((p) >= (void*)vm->m_stack_top) & ((p) < (void*)vm->m_stack_limit))