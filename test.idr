import public Language.Reflection

%language ElabReflection

interface ParamRet a where
  desc : String

ParamRet Bool where
  desc = "ABIBool"

ParamRet Int where
  desc = "ABIInt"

genABI : Name -> (tp: TTImp) -> TTImp
genABI fnName (IPi _ _ AutoImplicit _ _ rest) = genABI fnName rest
genABI fnName (IPi _ _ ImplicitArg _ _ rest) = genABI fnName rest
genABI fnName (IPi _ _ ExplicitArg _ argTy rest) = `(desc {a= ~(argTy)} ++ "->" ++ ~(genABI fnName rest))
genABI fnName resultTy = `(desc {a= ~(resultTy)})

-- public export %macro
abi : Name -> Elab String
abi fName = do
  [(name, tp)] <- getType fName
               | _ => failAt EmptyFC ("Unknown or ambigous function in entry point: " ++ show fName)
  logTerm "" 0 "type" tp
  logMsg "" 0 (show fName)
  str <- check $ genABI name tp
  pure str

f : Bool -> Int -> Bool
f b q = b || q > 0 





  
  
