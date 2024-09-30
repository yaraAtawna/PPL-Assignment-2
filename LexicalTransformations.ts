import { ClassExp, ProcExp, Exp, Program, CExp, Binding, makeIfExp, makeAppExp, makePrimOp, makeVarDecl, makeVarRef, makeBoolExp, makeLitExp, makeProcExp, isNumExp, isBoolExp, isStrExp, isPrimOp, isVarRef, isLitExp, isIfExp, isProcExp, isClassExp, isAppExp, isLetExp, isAtomicExp, isCExp, isDefineExp, makeDefineExp, DefineExp, isProgram, isExp, makeProgram, makeBinding, LetExp, makeLetExp } from "./L3-ast";
import { Result, bind, makeFailure, makeOk, mapResult, mapv } from "../shared/result";
import { map, reduce, reverse } from "ramda";
import { makeSymbolSExp } from "./L3-value";
import { applyEnv } from "./L3-env-env";

/*
Purpose: Transform ClassExp to ProcExp
Signature: class2proc(classExp)
Type: ClassExp => ProcExp
*/
//export const makeBoolExp1 = (): CExp => makeBoolExp(false);
export const class2proc = (exp: ClassExp): ProcExp => 
    makeProcExp(exp.fields, [
        makeProcExp([makeVarDecl("msg")], [
            reduce(
                (acc: CExp, b: Binding): CExp => 
                    makeIfExp(
                        makeAppExp(makePrimOp("eq?"), [makeVarRef("msg"), makeLitExp(makeSymbolSExp(b.var.var))]),
                        makeAppExp(b.val, []),
                        acc
                    ),
                makeBoolExp(false),
                reverse(exp.methods)
            )
        ])
    ]);


/*
Purpose: Transform all class forms in the given AST to procs
Signature: lexTransform(AST)
Type: [Exp | Program] => Result<Exp | Program>
*/

export const lexTransform = (exp: Exp | Program): Result<Exp | Program> =>
    isExp(exp) ? lexTransformExp(exp) : 
    isProgram(exp) ? mapv(mapResult(lexTransformExp, exp.exps), makeProgram) : 
    makeOk(exp);
const lexTransformExp = (exp: Exp): Result<Exp> => 
    isCExp(exp) ? lexTransformCExp(exp) :
    isDefineExp(exp) ? mapv(lexTransformCExp(exp.val), (val: CExp): DefineExp => makeDefineExp(exp.var, val)) :
    makeOk(exp);

const lexTransformCExp = (exp: CExp): Result<CExp> => 
    isAtomicExp(exp) ? makeOk(exp) :
    isLitExp(exp) ? makeOk(exp) :
    isIfExp(exp) ? bind(lexTransformCExp(exp.test), (test: CExp) => 
                        bind(lexTransformCExp(exp.then), (then: CExp) => 
                            mapv(lexTransformCExp(exp.alt), (alt: CExp) => makeIfExp(test, then, alt)))) :
    isProcExp(exp) ? mapv(mapResult(lexTransformCExp, exp.body), (body: CExp[]): ProcExp => makeProcExp(exp.args, body)) :
    isClassExp(exp) ? makeOk(class2proc(exp)) : 
    isAppExp(exp) ? bind(lexTransformCExp(exp.rator), (rator: CExp): Result<CExp> => 
                        mapv(mapResult(lexTransformCExp, exp.rands), (rands: CExp[]) => makeAppExp(rator, rands))) :
    isLetExp(exp) ? bind(mapResult((b: Binding): Result<Binding> => mapv(lexTransformCExp(b.val), (val: CExp) => makeBinding(b.var.var, val)), exp.bindings), (bindings: Binding[]) =>
                        mapv(mapResult(lexTransformCExp, exp.body), (body: CExp[]): LetExp => makeLetExp(bindings, body))) :
    makeOk(exp);
