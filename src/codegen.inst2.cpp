extern scm_obj_t subr_num_eq(VM* vm, int argc, scm_obj_t argv[]);

AllocaInst*
codegen_t::CreateEntryBlockAlloca(context_t& ctx, llvm::Type* type)
{
    DECLEAR_CONTEXT_VARS;
    DECLEAR_COMMON_TYPES;
    IRBuilder<> TB(&F->getEntryBlock(), F->getEntryBlock().begin());
    return TB.CreateAlloca(type);
}

void
codegen_t::emit_subr_a2_maybe_fail_num_eq(context_t& ctx, scm_obj_t inst, scm_subr_t subr, AllocaInst* ans, BasicBlock* CONTINUE, BasicBlock* FALLBACK)
{
    //puts("emit_subr_a2_maybe_fail_num_eq");
    DECLEAR_CONTEXT_VARS;
    DECLEAR_COMMON_TYPES;
    scm_obj_t operands = CDAR(inst);
    auto vm = F->arg_begin();

    auto sp = ctx.reg_sp.load(vm);
    auto sp_minus_1 = IRB.CreateLoad(IRB.CreateGEP(IRB.CreateBitOrPointerCast(sp, IntptrPtrTy), VALUE_INTPTR(-1)));
    auto sp_minus_2 = IRB.CreateLoad(IRB.CreateGEP(IRB.CreateBitOrPointerCast(sp, IntptrPtrTy), VALUE_INTPTR(-2)));

    BasicBlock* fixnum_true = BasicBlock::Create(C, "fixnum_true", F);
    auto fixnum_cond = IRB.CreateICmpNE(IRB.CreateAnd(IRB.CreateAnd(sp_minus_1, sp_minus_2), 1), VALUE_INTPTR(0));
    IRB.CreateCondBr(fixnum_cond, fixnum_true, FALLBACK);

    IRB.SetInsertPoint(fixnum_true);
    BasicBlock* num_eq_true = BasicBlock::Create(C, "num_eq_true", F);
    BasicBlock* num_eq_false = BasicBlock::Create(C, "num_eq_false", F);
    auto eq_cond = IRB.CreateICmpEQ(sp_minus_1, sp_minus_2);
    IRB.CreateCondBr(eq_cond, num_eq_true, num_eq_false);

    IRB.SetInsertPoint(num_eq_true);
    IRB.CreateStore(VALUE_INTPTR(scm_true), ans);
    IRB.CreateBr(CONTINUE);

    IRB.SetInsertPoint(num_eq_false);
    IRB.CreateStore(VALUE_INTPTR(scm_false), ans);
    IRB.CreateBr(CONTINUE);
}

void
codegen_t::emit_subr_a2_maybe_fail(context_t& ctx, scm_obj_t inst, scm_subr_t subr)
{
    DECLEAR_CONTEXT_VARS;
    DECLEAR_COMMON_TYPES;
    scm_obj_t operands = CDAR(inst);
    auto vm = F->arg_begin();

    intptr_t argc = FIXNUM(CADR(operands));

    BasicBlock* CONTINUE = BasicBlock::Create(C, "continue", F);
    BasicBlock* FALLBACK = BasicBlock::Create(C, "fallback", F);

    auto ans = CreateEntryBlockAlloca(ctx, IntptrTy);

    if (subr->adrs == subr_num_eq) {
        emit_subr_a2_maybe_fail_num_eq(ctx, inst, subr, ans, CONTINUE, FALLBACK);
    }

    IRB.SetInsertPoint(FALLBACK);
    auto sp = ctx.reg_sp.load(vm);
    CREATE_STORE_VM_REG(vm, m_pc, VALUE_INTPTR(inst));
    auto argv = IRB.CreateSub(sp, VALUE_INTPTR(argc << log2_of_intptr_size()));
    auto subrType = FunctionType::get(IntptrTy, { IntptrPtrTy, IntptrTy, IntptrTy }, false);
    auto ptr = ConstantExpr::getIntToPtr(VALUE_INTPTR(subr->adrs), subrType->getPointerTo());
    auto val = IRB.CreateCall(ptr, { vm, VALUE_INTPTR(argc), argv });
    IRB.CreateStore(val, ans);
    BasicBlock* undef_true = BasicBlock::Create(C, "undef_true", F);
    auto undef_cond = IRB.CreateICmpEQ(val, VALUE_INTPTR(scm_undef));
    IRB.CreateCondBr(undef_cond, undef_true, CONTINUE);

    // invalid
    IRB.SetInsertPoint(undef_true);
    ctx.reg_cache_copy_except_sp(vm);
    IRB.CreateRet(VALUE_INTPTR(VM::native_thunk_resume_loop));

    IRB.SetInsertPoint(CONTINUE);
    ctx.reg_sp.store(vm, IRB.CreateSub(ctx.reg_sp.load(vm), VALUE_INTPTR(argc << log2_of_intptr_size())));
    ctx.reg_value.store(vm, IRB.CreateLoad(ans));
}

void
codegen_t::emit_subr(context_t& ctx, scm_obj_t inst, scm_subr_t subr)
{
    DECLEAR_CONTEXT_VARS;
    DECLEAR_COMMON_TYPES;
    scm_obj_t operands = CDAR(inst);
    auto vm = F->arg_begin();

    intptr_t argc = FIXNUM(CADR(operands));

#if ENABLE_INLINE_SUBR
    if (argc == 2) {
        if (subr->adrs == subr_num_eq) {
            emit_subr_a2_maybe_fail(ctx, inst, subr);
            return;
        }
    }
#endif

    BasicBlock* CONTINUE = BasicBlock::Create(C, "continue", F);

    auto sp = ctx.reg_sp.load(vm);
    auto argv = IRB.CreateSub(sp, VALUE_INTPTR(argc << log2_of_intptr_size()));

    CREATE_STORE_VM_REG(vm, m_pc, VALUE_INTPTR(inst));
    auto subrType = FunctionType::get(IntptrTy, { IntptrPtrTy, IntptrTy, IntptrTy }, false);
    auto ptr = ConstantExpr::getIntToPtr(VALUE_INTPTR(subr->adrs), subrType->getPointerTo());
    auto val = IRB.CreateCall(ptr, { vm, VALUE_INTPTR(argc), argv });

    BasicBlock* undef_true = BasicBlock::Create(C, "undef_true", F);
    auto undef_cond = IRB.CreateICmpEQ(val, VALUE_INTPTR(scm_undef));
    IRB.CreateCondBr(undef_cond, undef_true, CONTINUE);

    // invalid
    IRB.SetInsertPoint(undef_true);
    ctx.reg_cache_copy_except_sp(vm);
    IRB.CreateRet(VALUE_INTPTR(VM::native_thunk_resume_loop));

    IRB.SetInsertPoint(CONTINUE);
    ctx.reg_sp.store(vm, IRB.CreateSub(ctx.reg_sp.load(vm), VALUE_INTPTR(argc << log2_of_intptr_size())));
    ctx.reg_value.store(vm, val);
}

void
codegen_t::emit_ret_subr(context_t& ctx, scm_obj_t inst, scm_subr_t subr)
{
    DECLEAR_CONTEXT_VARS;
    DECLEAR_COMMON_TYPES;
    scm_obj_t operands = CDAR(inst);
    auto vm = F->arg_begin();

    auto sp = ctx.reg_sp.load(vm);
    auto fp = ctx.reg_fp.load(vm);
    auto argc = VALUE_INTPTR(ctx.m_argc);

    CREATE_STORE_VM_REG(vm, m_pc, VALUE_INTPTR(inst));
    auto subrType = FunctionType::get(IntptrTy, { IntptrPtrTy, IntptrTy, IntptrTy }, false);
    auto ptr = ConstantExpr::getIntToPtr(VALUE_INTPTR(subr->adrs), subrType->getPointerTo());
    auto val = IRB.CreateCall(ptr, { vm, argc, fp });

    ctx.reg_value.store(vm, val);

    BasicBlock* undef_true = BasicBlock::Create(C, "undef_true", F);
    BasicBlock* undef_false = BasicBlock::Create(C, "undef_false", F);
    auto undef_cond = IRB.CreateICmpEQ(val, VALUE_INTPTR(scm_undef));
    IRB.CreateCondBr(undef_cond, undef_true, undef_false);

    // valid
    IRB.SetInsertPoint(undef_false);
    ctx.reg_cache_copy_only_value_and_cont(vm);
    IRB.CreateRet(VALUE_INTPTR(VM::native_thunk_pop_cont));

    // invalid
    IRB.SetInsertPoint(undef_true);
    ctx.reg_cache_copy_except_sp(vm);
    IRB.CreateRet(VALUE_INTPTR(VM::native_thunk_resume_loop));
}
