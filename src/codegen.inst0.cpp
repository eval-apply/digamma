
Function*
codegen_t::emit_prepare_call(context_t& ctx)
{
    LLVMContext& C = ctx.m_llvm_context;
    Module* M = ctx.m_module;

    DECLEAR_COMMON_TYPES;

    Function* F = Function::Create(FunctionType::get(VoidTy, {IntptrPtrTy, IntptrPtrTy}, false), Function::WeakAnyLinkage, "prepare_call", M);
    F->setCallingConv(CallingConv::Fast);
#if USE_LLVM_ATTRIBUTES
    F->addFnAttr(Attribute::NoUnwind);
    F->addParamAttr(0, Attribute::NoAlias);
    F->addParamAttr(0, Attribute::NoCapture);
    F->addParamAttr(1, Attribute::NoAlias);
    F->addParamAttr(1, Attribute::NoCapture);
#endif

    IRBuilder<> IRB(BasicBlock::Create(C, "entry", F));
    auto vm = F->arg_begin();
    auto cont = F->arg_begin() + 1;

    CREATE_STORE_CONT_REC(cont, trace, VALUE_INTPTR(scm_unspecified));
    // cont->fp = m_fp;
    CREATE_STORE_CONT_REC(cont, fp, CREATE_LOAD_VM_REG(vm, m_fp));
    // cont->env = m_env;
    CREATE_STORE_CONT_REC(cont, env, CREATE_LOAD_VM_REG(vm, m_env));
    // cont->up = m_cont;
    CREATE_STORE_CONT_REC(cont, up, CREATE_LOAD_VM_REG(vm, m_cont));
    // m_sp = m_fp = (scm_obj_t*)(cont + 1);
    auto ea1 = IRB.CreateBitOrPointerCast(IRB.CreateGEP(cont, VALUE_INTPTR(sizeof(vm_cont_rec_t) / sizeof(intptr_t))), IntptrTy);
    CREATE_STORE_VM_REG(vm, m_sp, ea1);
    CREATE_STORE_VM_REG(vm, m_fp, ea1);
    // m_cont = &cont->up;
    auto ea2 = IRB.CreateBitOrPointerCast(IRB.CreateGEP(cont, VALUE_INTPTR(offsetof(vm_cont_rec_t, up) / sizeof(intptr_t))), IntptrTy);
    CREATE_STORE_VM_REG(vm, m_cont, ea2);
    IRB.CreateRetVoid();

    return F;
}

Function*
codegen_t::emit_inner_function(context_t& ctx, scm_closure_t closure)
{
    VM* vm = m_vm;

    auto search = m_lifted_functions.find(closure);
    if (search != m_lifted_functions.end()) {
#if DEBUG_CODEGEN
      puts(" + found in m_lifted_functions, return Function*");
#endif
      return search->second;
    }

    if (is_compiled(closure)) {
#if DEBUG_CODEGEN
        puts(" + emit_inner_function: already compiled");
#endif
        return get_function(ctx, closure);
    }

#if DEBUG_CODEGEN
    puts(" + generating native code for lifted function");
#endif

    char function_id[40];
    uuid_v4(function_id, sizeof(function_id));

    LLVMContext& C = ctx.m_llvm_context;
    Module* M = ctx.m_module;

    DECLEAR_COMMON_TYPES;

    Function* F = Function::Create(FunctionType::get(IntptrTy, {IntptrPtrTy}, false), Function::ExternalLinkage, function_id, M);
#if USE_LLVM_ATTRIBUTES
    F->addFnAttr(Attribute::NoUnwind);
    F->addParamAttr(0, Attribute::NoAlias);
    F->addParamAttr(0, Attribute::NoCapture);
#endif

    BasicBlock* ENTRY = BasicBlock::Create(C, "entry", F);
    IRBuilder<> IRB(ENTRY);

    m_lifted_functions.insert({closure, F});

    context_t context(C, IRB);
    context.m_module = M;
    context.m_function = F;
    context.m_top_level_closure = closure;
    context.m_top_level_function = F;
    context.m_intrinsics = ctx.m_intrinsics;

    transform(context, closure->pc, true);

    return F;
}

void
codegen_t::emit_stack_overflow_check(context_t& ctx, int nbytes)
{
    DECLEAR_CONTEXT_VARS;
    DECLEAR_COMMON_TYPES;
    auto vm = F->arg_begin();

    if (nbytes) {
        if (nbytes >= VM_STACK_BYTESIZE) fatal("%s:%u vm stack size too small", __FILE__, __LINE__);
        // printf("emit_stack_overflow_check: %d\n", nbytes);
        auto sp = CREATE_LOAD_VM_REG(vm, m_sp);
        auto stack_limit = CREATE_LOAD_VM_REG(vm, m_stack_limit);
        BasicBlock* stack_ok = BasicBlock::Create(C, "stack_ok", F);
        BasicBlock* stack_overflow = BasicBlock::Create(C, "stack_overflow", F);
        Value* stack_cond = IRB.CreateICmpULT(IRB.CreateAdd(sp, VALUE_INTPTR(nbytes)), stack_limit);
        IRB.CreateCondBr(stack_cond, stack_ok, stack_overflow);
        IRB.SetInsertPoint(stack_overflow);
        auto c_collect_stack = M->getOrInsertFunction("c_collect_stack", VoidTy, IntptrPtrTy, IntptrTy);
        IRB.CreateCall(c_collect_stack, {vm, VALUE_INTPTR(nbytes)});
        IRB.CreateBr(stack_ok);
        IRB.SetInsertPoint(stack_ok);
    }
}

Value*
codegen_t::emit_lookup_env(context_t& ctx, intptr_t depth)
{
    DECLEAR_CONTEXT_VARS;
    DECLEAR_COMMON_TYPES;
    auto vm = F->arg_begin();

    // [TODO] optimize
    if (depth == 0) {
        auto env = IRB.CreateBitOrPointerCast(IRB.CreateSub(CREATE_LOAD_VM_REG(vm, m_env), VALUE_INTPTR(offsetof(vm_env_rec_t, up))), IntptrPtrTy);
        return env;
    } else if (depth == 1) {
        auto lnk1 = IRB.CreateLoad(IRB.CreateBitOrPointerCast(CREATE_LOAD_VM_REG(vm, m_env), IntptrPtrTy));
        auto env = IRB.CreateBitOrPointerCast(IRB.CreateSub(lnk1, VALUE_INTPTR(offsetof(vm_env_rec_t, up))), IntptrPtrTy);
        return env;
    } else if (depth == 2) {
        auto lnk1 = IRB.CreateLoad(IRB.CreateBitOrPointerCast(CREATE_LOAD_VM_REG(vm, m_env), IntptrPtrTy));
        auto lnk2 = IRB.CreateLoad(IRB.CreateBitOrPointerCast(lnk1, IntptrPtrTy));
        auto env = IRB.CreateBitOrPointerCast(IRB.CreateSub(lnk2, VALUE_INTPTR(offsetof(vm_env_rec_t, up))), IntptrPtrTy);
        return env;
    } else if (depth == 3) {
        auto lnk1 = IRB.CreateLoad(IRB.CreateBitOrPointerCast(CREATE_LOAD_VM_REG(vm, m_env), IntptrPtrTy));
        auto lnk2 = IRB.CreateLoad(IRB.CreateBitOrPointerCast(lnk1, IntptrPtrTy));
        auto lnk3 = IRB.CreateLoad(IRB.CreateBitOrPointerCast(lnk2, IntptrPtrTy));
        auto env = IRB.CreateBitOrPointerCast(IRB.CreateSub(lnk3, VALUE_INTPTR(offsetof(vm_env_rec_t, up))), IntptrPtrTy);
        return env;
    } else if (depth == 4) {
        auto lnk1 = IRB.CreateLoad(IRB.CreateBitOrPointerCast(CREATE_LOAD_VM_REG(vm, m_env), IntptrPtrTy));
        auto lnk2 = IRB.CreateLoad(IRB.CreateBitOrPointerCast(lnk1, IntptrPtrTy));
        auto lnk3 = IRB.CreateLoad(IRB.CreateBitOrPointerCast(lnk2, IntptrPtrTy));
        auto lnk4 = IRB.CreateLoad(IRB.CreateBitOrPointerCast(lnk3, IntptrPtrTy));
        auto env = IRB.CreateBitOrPointerCast(IRB.CreateSub(lnk4, VALUE_INTPTR(offsetof(vm_env_rec_t, up))), IntptrPtrTy);
        return env;
    }
    auto c_lookup_env = M->getOrInsertFunction("c_lookup_env", IntptrPtrTy, IntptrPtrTy, IntptrTy);
    return IRB.CreateCall(c_lookup_env, { vm, VALUE_INTPTR(depth) });
}

Value*
codegen_t::emit_lookup_iloc(context_t& ctx, intptr_t depth, intptr_t index)
{
    DECLEAR_CONTEXT_VARS;
    DECLEAR_COMMON_TYPES;
    auto vm = F->arg_begin();

    if (depth <= 4) {
        auto env = emit_lookup_env(ctx, depth);
        auto count = CREATE_LOAD_ENV_REC(env, count);
        if (index == 0) return IRB.CreateGEP(env, IRB.CreateNeg(count));
        return IRB.CreateGEP(env, IRB.CreateSub(VALUE_INTPTR(index), count));
    }
    auto c_lookup_iloc = M->getOrInsertFunction("c_lookup_iloc", IntptrPtrTy, IntptrPtrTy, IntptrTy, IntptrTy);
    return IRB.CreateCall(c_lookup_iloc, { vm, VALUE_INTPTR(depth), VALUE_INTPTR(index) });
}

Value*
codegen_t::emit_lookup_iloc(context_t& ctx, scm_obj_t loc)
{
    return emit_lookup_iloc(ctx, FIXNUM(CAR(loc)), FIXNUM(CDR(loc)));
}