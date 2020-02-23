// Copyright (c) 2004-2020 Yoshikatsu Fujita / LittleWing Company Limited.
// See LICENSE file for terms and conditions of use.

#include "core.h"
#include "object.h"
#include "vm.h"

#include "llvm/ExecutionEngine/Orc/LLJIT.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"

#if __clang_major__ > 9
using namespace std;
#endif

using namespace llvm;
using namespace llvm::orc;

class codegen_t {
    struct context_t {
        LLVMContext& m_llvm_context;
        Module* m_module;
        Function* m_function;
        IRBuilder<>& m_irb;
        scm_closure_t m_top_level_closure;
        Function* m_top_level_function;
        std::vector<Function*> m_local_functions;
        int m_argc;
        int m_depth;
        context_t(LLVMContext& llvm_context, IRBuilder<>& irb) : m_llvm_context(llvm_context), m_irb(irb), m_argc(0), m_depth(0) {}
    };
    enum cc_t {
        LT,
        GT,
        LE,
        GE,
        EQ,
    };

    std::unique_ptr<LLJIT> m_jit;
    ThreadSafeModule optimizeModule(ThreadSafeModule TSM);
    void define_prepare_call();
    void transform(context_t ctx, scm_obj_t inst);
    bool is_compiled(VM* vm, scm_closure_t closure);
public:
    codegen_t();
    void compile(VM* vm, scm_closure_t closure);
private:
    Value* emit_lookup_env(context_t& ctx, intptr_t depth);
    Value* emit_lookup_iloc(context_t& ctx, intptr_t depth, intptr_t index);
    Value* emit_lookup_iloc(context_t& ctx, scm_obj_t inst);
    Value* emit_cmp_inst(context_t& ctx, cc_t cc, Value* lhs, Value* rhs);
    void emit_cc_n_iloc(context_t& ctx, scm_obj_t inst, cc_t cc, const char* cfunc);
    void emit_cc_iloc(context_t& ctx, scm_obj_t inst, cc_t cc, const char* cfunc);
    Function* emit_call(context_t& ctx, scm_obj_t inst);

    void emit_subr(context_t& ctx, scm_obj_t inst);

    void emit_push(context_t& ctx, scm_obj_t inst);
    void emit_push_const(context_t& ctx, scm_obj_t inst);
    void emit_push_iloc0(context_t& ctx, scm_obj_t inst);
    void emit_push_iloc1(context_t& ctx, scm_obj_t inst);
    void emit_push_gloc(context_t& ctx, scm_obj_t inst);
    void emit_push_subr(context_t& ctx, scm_obj_t inst);
    void emit_push_car_iloc(context_t& ctx, scm_obj_t inst);
    void emit_push_cdr_iloc(context_t& ctx, scm_obj_t inst);
    void emit_push_cddr_iloc(context_t& ctx, scm_obj_t inst);
    void emit_push_nadd_iloc(context_t& ctx, scm_obj_t inst);
    void emit_push_iloc(context_t& ctx, scm_obj_t inst);

    void emit_apply_iloc(context_t& ctx, scm_obj_t inst);
    void emit_apply_gloc(context_t& ctx, scm_obj_t inst);

    void emit_ret_const(context_t& ctx, scm_obj_t inst);
    void emit_ret_iloc(context_t& ctx, scm_obj_t inst);
    void emit_ret_cons(context_t& ctx, scm_obj_t inst);
    void emit_ret_subr(context_t& ctx, scm_obj_t inst);

    void emit_if_true(context_t& ctx, scm_obj_t inst);
    void emit_if_nullp(context_t& ctx, scm_obj_t inst);
    void emit_if_nullp_ret_const(context_t& ctx, scm_obj_t inst);
    void emit_if_true_ret(context_t& ctx, scm_obj_t inst);

    void emit_iloc0(context_t& ctx, scm_obj_t inst);
    void emit_lt_n_iloc(context_t& ctx, scm_obj_t inst);
    void emit_gt_n_iloc(context_t& ctx, scm_obj_t inst);
    void emit_extend(context_t& ctx, scm_obj_t inst);
    void emit_extend_enclose_local(context_t& ctx, scm_obj_t inst);
    void emit_apply_iloc_local(context_t& ctx, scm_obj_t inst);
    void emit_if_true_ret_const(context_t& ctx, scm_obj_t inst);
    void emit_lt_iloc(context_t& ctx, scm_obj_t inst);
    void emit_gt_iloc(context_t& ctx, scm_obj_t inst);
};

/*
(backtrace #f)
(import (digamma time))

(define (fib n)
  (if (< n 2)
    n
    (+ (fib (- n 1))
       (fib (- n 2)))))
(closure-compile fib)
(time (fib 40)) ;=> 102334155

macbook default
;; 18.153539 real   18.145671 user    0.005424 sys
macbook jit
;;  8.706625 real    8.699991 user    0.004582 sys
   (7.350153 real    7.345971 user    0.002947 sys)
*/