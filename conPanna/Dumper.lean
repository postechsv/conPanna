import conPanna.Dumper.Base
import conPanna.Reflect.Model

/-!
`#dump_model T`: write the constructor model of state type `T` for the producer
(`Dumper/Base.lean`), and define its reflection model `T.reflect.model` with its laws
(`Reflect/Model.lean`), which certification by reflection uses.
-/

namespace Dumper

open Lean Meta Elab Command

/-- `#dump_model T`: write the model files of state type `T` into `outDir`, and define the
reflection model `T.reflect.model`. -/
syntax (name := dumpModel) "#dump_model " term : command

@[command_elab dumpModel] def elabDumpModel : CommandElab
  | `(#dump_model $t) => do
    let st ← liftTermElabM do
      let ty ← Term.elabType t
      let st ← model ty
      if let some b := Reflect.Tac.baseOf ty then
        unless (← getEnv).contains (b ++ `model) do
          discard <| Reflect.Tac.mkModel (← Reflect.Tac.mkTbl st) (some b)
      return st
    liftCoreM (write st)
    logInfo m!"{render st}\nwrote {← liftCoreM (modelPath st)} and its .json"
  | _ => throwUnsupportedSyntax

end Dumper
