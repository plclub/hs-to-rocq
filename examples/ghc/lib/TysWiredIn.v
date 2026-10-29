(* Default settings (from HsToRocq.Rocq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require AxiomatizedTypes.
Require BasicTypes.
Require Core.
Require FastString.
Require GHC.Base.
Require GHC.Core.Map.Type.
Require HsSyn.
Require Module.
Require Name.
Require OccName.
Require PrelNames.
Require UniqSet.
Require Unique.

(* Converted type declarations: *)

Inductive BoxingInfo b : Type :=
  | BI_NoBoxNeeded : BoxingInfo b
  | BI_NoBoxAvailable : BoxingInfo b
  | BI_Box (bi_data_con : Core.DataCon) (bi_inst_con : Core.Expr b) (bi_boxed_type
    : AxiomatizedTypes.Type_)
   : BoxingInfo b.

Arguments BI_NoBoxNeeded {_}.

Arguments BI_NoBoxAvailable {_}.

Arguments BI_Box {_} _ _ _.

(* Converted value declarations: *)

Axiom alpha_tyvar : list Core.TyVar.

Axiom alpha_ty : list AxiomatizedTypes.Type_.

Axiom wiredInTyCons : list Core.TyCon.

Axiom mkWiredInTyConName : Name.BuiltInSyntax ->
                           Module.Module ->
                           FastString.FastString -> Unique.Unique -> Core.TyCon -> Name.Name.

Axiom mkWiredInDataConName : Name.BuiltInSyntax ->
                             Module.Module ->
                             FastString.FastString -> Unique.Unique -> Core.DataCon -> Name.Name.

Axiom mkWiredInIdName : Module.Module ->
                        FastString.FastString -> Unique.Unique -> Core.Id -> Name.Name.

Axiom eqTyConName : Name.Name.

Axiom eqDataConName : Name.Name.

Axiom eqSCSelIdName : Name.Name.

Axiom eqTyCon_RDR : PrelNames.RdrName.

Axiom heqTyConName : Name.Name.

Axiom heqDataConName : Name.Name.

Axiom heqSCSelIdName : Name.Name.

Axiom coercibleTyConName : Name.Name.

Axiom coercibleDataConName : Name.Name.

Axiom coercibleSCSelIdName : Name.Name.

Axiom charTyConName : Name.Name.

Axiom charDataConName : Name.Name.

Axiom stringTyConName : Name.Name.

Axiom intTyConName : Name.Name.

Axiom intDataConName : Name.Name.

Axiom boolTyConName : Name.Name.

Axiom falseDataConName : Name.Name.

Axiom trueDataConName : Name.Name.

Axiom listTyConName : Name.Name.

Axiom nilDataConName : Name.Name.

Axiom consDataConName : Name.Name.

Axiom maybeTyConName : Name.Name.

Axiom nothingDataConName : Name.Name.

Axiom justDataConName : Name.Name.

Axiom wordTyConName : Name.Name.

Axiom wordDataConName : Name.Name.

Axiom word8DataConName : Name.Name.

Axiom floatTyConName : Name.Name.

Axiom floatDataConName : Name.Name.

Axiom doubleTyConName : Name.Name.

Axiom doubleDataConName : Name.Name.

Axiom anyTyConName : Name.Name.

Axiom anyTyCon : Core.TyCon.

Axiom anyTy : AxiomatizedTypes.Type_.

Axiom anyTypeOfKind : AxiomatizedTypes.Kind -> AxiomatizedTypes.Type_.

Axiom zonkAnyTyConName : Name.Name.

Axiom zonkAnyTyCon : Core.TyCon.

Axiom makeRecoveryTyCon : Core.TyCon -> Core.TyCon.

Axiom typeSymbolKindConName : Name.Name.

Axiom boolTyCon_RDR : PrelNames.RdrName.

Axiom false_RDR : PrelNames.RdrName.

Axiom true_RDR : PrelNames.RdrName.

Axiom intTyCon_RDR : PrelNames.RdrName.

Axiom charTyCon_RDR : PrelNames.RdrName.

Axiom stringTyCon_RDR : PrelNames.RdrName.

Axiom intDataCon_RDR : PrelNames.RdrName.

Axiom listTyCon_RDR : PrelNames.RdrName.

Axiom consDataCon_RDR : PrelNames.RdrName.

Axiom pcTyCon : Name.Name ->
                option AxiomatizedTypes.CType ->
                list Core.TyVar -> list Core.DataCon -> Core.TyCon.

Axiom pcDataCon : Name.Name ->
                  list Core.TyVar -> list AxiomatizedTypes.Type_ -> Core.TyCon -> Core.DataCon.

Axiom pcRepPolyDataCon : Name.Name ->
                         list Core.TyVar ->
                         TcType.ConcreteTyVars ->
                         list AxiomatizedTypes.Type_ -> Core.TyCon -> Core.DataCon.

Axiom pcDataConConstraint : Name.Name ->
                            list Core.TyVar -> AxiomatizedTypes.ThetaType -> Core.TyCon -> Core.DataCon.

Axiom pcSpecialDataCon : Name.Name ->
                         list AxiomatizedTypes.Type_ ->
                         Core.TyCon -> Core.PromDataConInfo -> Core.DataCon.

Axiom pcDataConWithFixity : bool ->
                            Name.Name ->
                            list Core.TyVar ->
                            list Core.TyCoVar ->
                            TcType.ConcreteTyVars ->
                            list Core.TyCoVar ->
                            AxiomatizedTypes.ThetaType ->
                            list (Core.Scaled AxiomatizedTypes.Type_) -> Core.TyCon -> Core.DataCon.

Axiom pcDataConWithFixity' : bool ->
                             Name.Name ->
                             Unique.Unique ->
                             Core.PromDataConInfo ->
                             list Core.TyVar ->
                             list Core.TyCoVar ->
                             TcType.ConcreteTyVars ->
                             list Core.TyCoVar ->
                             AxiomatizedTypes.ThetaType ->
                             list (Core.Scaled AxiomatizedTypes.Type_) -> Core.TyCon -> Core.DataCon.

Axiom mkDataConWorkerName : Core.DataCon -> Unique.Unique -> Name.Name.

Axiom typeSymbolKindCon : Core.TyCon.

Axiom typeSymbolKind : AxiomatizedTypes.Kind.

Axiom isBuiltInOcc_maybe : OccName.OccName -> option Name.Name.

Axiom isTupleTyOcc_maybe : Module.Module -> OccName.OccName -> option Name.Name.

Axiom isCTupleOcc_maybe : Module.Module -> OccName.OccName -> option Name.Name.

Axiom isTupleNTyOcc_maybe : OccName.OccName -> option Name.Name.

Axiom isSumTyOcc_maybe : Module.Module -> OccName.OccName -> option Name.Name.

Axiom isSumNTyOcc_maybe : OccName.OccName -> option Name.Name.

Axiom arity_and_boxity : GHC.Base.String ->
                         option (BasicTypes.TupleSort * nat)%type.

Axiom isPunOcc_maybe : Module.Module -> OccName.OccName -> option Name.Name.

Axiom mkTupleOcc : OccName.NameSpace ->
                   HsSyn.Boxity -> BasicTypes.Arity -> (OccName.OccName * Name.BuiltInSyntax)%type.

Axiom mkCTupleOcc : OccName.NameSpace -> BasicTypes.Arity -> OccName.OccName.

Axiom mkTupleStr : HsSyn.Boxity ->
                   OccName.NameSpace -> BasicTypes.Arity -> GHC.Base.String.

Axiom mkTupleStr' : OccName.NameSpace ->
                    HsSyn.Boxity -> BasicTypes.Arity -> (GHC.Base.String * Name.BuiltInSyntax)%type.

Axiom mkConstraintTupleStr : BasicTypes.Arity -> GHC.Base.String.

Axiom commas : BasicTypes.Arity -> GHC.Base.String.

Axiom cTupleTyCon : BasicTypes.Arity -> Core.TyCon.

Axiom cTupleTyConName : BasicTypes.Arity -> Name.Name.

Axiom cTupleTyConNames : list Name.Name.

Axiom cTupleTyConKeys : UniqSet.UniqSet Unique.Unique.

Axiom isCTupleTyConName : Name.Name -> bool.

Axiom cTupleTyConNameArity_maybe : Name.Name -> option BasicTypes.Arity.

Axiom cTupleDataCon : BasicTypes.Arity -> Core.DataCon.

Axiom cTupleDataConName : BasicTypes.Arity -> Name.Name.

Axiom cTupleDataConNames : list Name.Name.

Axiom cTupleSelId : HsSyn.ConTag -> BasicTypes.Arity -> Core.Id.

Axiom cTupleSelIdName : HsSyn.ConTag -> BasicTypes.Arity -> Name.Name.

Axiom tupleTyCon : HsSyn.Boxity -> BasicTypes.Arity -> Core.TyCon.

Axiom tupleTyConName : BasicTypes.TupleSort -> BasicTypes.Arity -> Name.Name.

Axiom promotedTupleDataCon : HsSyn.Boxity -> BasicTypes.Arity -> Core.TyCon.

Axiom tupleDataCon : HsSyn.Boxity -> BasicTypes.Arity -> Core.DataCon.

Axiom tupleDataConName : HsSyn.Boxity -> BasicTypes.Arity -> Name.Name.

Axiom mkPromotedPairTy : AxiomatizedTypes.Kind ->
                         AxiomatizedTypes.Kind ->
                         AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom isPromotedPairType : AxiomatizedTypes.Type_ ->
                           option (AxiomatizedTypes.Type_ * AxiomatizedTypes.Type_)%type.

(* Skipping definition `TysWiredIn.boxedTupleArr' *)

(* Skipping definition `TysWiredIn.unboxedTupleArr' *)

(* Skipping definition `TysWiredIn.cTupleArr' *)

Axiom unboxedTupleSumKind : Core.TyCon ->
                            list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Kind.

Axiom unboxedTupleKind : list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Kind.

Axiom mk_tuple : HsSyn.Boxity -> nat -> (Core.TyCon * Core.DataCon)%type.

(* Skipping definition `TysWiredIn.mk_ctuple' *)

Axiom unitTyCon : Core.TyCon.

Axiom unitTyConName : Name.Name.

Axiom unitTyConKey : Unique.Unique.

Axiom unitDataCon : Core.DataCon.

Axiom unitDataConId : Core.Id.

Axiom soloTyCon : Core.TyCon.

Axiom soloTyConName : Name.Name.

Axiom soloDataConName : Name.Name.

Axiom pairTyCon : Core.TyCon.

Axiom unboxedUnitTy : AxiomatizedTypes.Type_.

Axiom unboxedUnitTyCon : Core.TyCon.

Axiom unboxedUnitTyConName : Name.Name.

Axiom unboxedUnitDataCon : Core.DataCon.

Axiom unboxedSoloTyCon : Core.TyCon.

Axiom unboxedSoloTyConName : Name.Name.

Axiom unboxedSoloDataConName : Name.Name.

Axiom mkSumTyConOcc : BasicTypes.Arity -> OccName.OccName.

Axiom mkSumDataConOcc : HsSyn.ConTag -> BasicTypes.Arity -> OccName.OccName.

Axiom sumTyCon : BasicTypes.Arity -> Core.TyCon.

Axiom sumDataCon : HsSyn.ConTag -> BasicTypes.Arity -> Core.DataCon.

(* Skipping definition `TysWiredIn.unboxedSumArr' *)

Axiom unboxedSumKind : list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Kind.

(* Skipping definition `TysWiredIn.mk_sum' *)

Axiom mk_class : Core.TyCon ->
                 AxiomatizedTypes.PredType -> Core.Id -> Core.Class.

Axiom mk_ctuple_class : Core.TyCon ->
                        AxiomatizedTypes.ThetaType -> list Core.Id -> Core.Class.

Axiom multiplicityTyConName : Name.Name.

Axiom oneDataConName : Name.Name.

Axiom manyDataConName : Name.Name.

Axiom multiplicityTy : AxiomatizedTypes.Type_.

Axiom multiplicityTyCon : Core.TyCon.

Axiom oneDataCon : Core.DataCon.

Axiom manyDataCon : Core.DataCon.

Axiom oneDataConTy : AxiomatizedTypes.Type_.

#[global] Definition manyDataConTyCon : Core.TyCon :=
  Core.promoteDataCon manyDataCon.

#[global] Definition manyDataConTy : AxiomatizedTypes.Type_ :=
  Core.mkTyConTy manyDataConTyCon.

Axiom oneDataConTyCon : Core.TyCon.

Axiom multMulTyConName : Name.Name.

Axiom multMulTyCon : Core.TyCon.

Axiom unrestrictedFunTyCon : Core.TyCon.

Axiom unrestrictedFunTyConName : Name.Name.

Axiom constraintKindTyCon : Core.TyCon.

Axiom constraintKindTyConName : Name.Name.

(* Skipping definition `AxiomatizedTypes.constraintKind' *)

Axiom liftedTypeKindTyCon : Core.TyCon.

Axiom liftedTypeKindTyConName : Name.Name.

(* Skipping definition `AxiomatizedTypes.liftedTypeKind' *)

Axiom typeToTypeKind : AxiomatizedTypes.Type_.

Axiom unliftedTypeKindTyCon : Core.TyCon.

Axiom unliftedTypeKindTyConName : Name.Name.

Axiom unliftedTypeKind : AxiomatizedTypes.Type_.

Axiom levityTyConName : Name.Name.

Axiom liftedDataConName : Name.Name.

Axiom unliftedDataConName : Name.Name.

Axiom levityTyCon : Core.TyCon.

Axiom levityTy : AxiomatizedTypes.Type_.

Axiom liftedDataCon : Core.DataCon.

Axiom unliftedDataCon : Core.DataCon.

Axiom liftedDataConTyCon : Core.TyCon.

Axiom unliftedDataConTyCon : Core.TyCon.

Axiom liftedDataConTy : AxiomatizedTypes.Type_.

Axiom unliftedDataConTy : AxiomatizedTypes.Type_.

Axiom runtimeRepTyCon : Core.TyCon.

Axiom runtimeRepTy : AxiomatizedTypes.Type_.

Axiom runtimeRepTyConName : Name.Name.

Axiom vecRepDataConName : Name.Name.

Axiom tupleRepDataConName : Name.Name.

Axiom sumRepDataConName : Name.Name.

Axiom boxedRepDataConName : Name.Name.

Axiom mk_runtime_rep_dc_name : FastString.FastString ->
                               Unique.Unique -> Core.DataCon -> Name.Name.

Axiom boxedRepDataCon : Core.DataCon.

Axiom boxedRepDataConTyCon : Core.TyCon.

Axiom tupleRepDataCon : Core.DataCon.

Axiom tupleRepDataConTyCon : Core.TyCon.

Axiom sumRepDataCon : Core.DataCon.

Axiom sumRepDataConTyCon : Core.TyCon.

Axiom runtimeRepSimpleDataCons : list Core.DataCon.

Axiom zeroBitRepTyCon : Core.TyCon.

Axiom zeroBitRepTyConName : Name.Name.

Axiom zeroBitRepTy : Core.RuntimeRepType.

Axiom zeroBitTypeTyCon : Core.TyCon.

Axiom zeroBitTypeTyConName : Name.Name.

Axiom zeroBitTypeKind : AxiomatizedTypes.Type_.

Axiom liftedRepTyCon : Core.TyCon.

Axiom liftedRepTyConName : Name.Name.

Axiom liftedRepTy : Core.RuntimeRepType.

Axiom unliftedRepTyCon : Core.TyCon.

Axiom unliftedRepTyConName : Name.Name.

Axiom unliftedRepTy : Core.RuntimeRepType.

Axiom vecCountTyConName : Name.Name.

Axiom vecElemTyConName : Name.Name.

Axiom vecRepDataCon : Core.DataCon.

Axiom vecRepDataConTyCon : Core.TyCon.

Axiom vecCountTyCon : Core.TyCon.

Axiom vecCountDataCons : list Core.DataCon.

Axiom vecElemTyCon : Core.TyCon.

Axiom vecElemDataCons : list Core.DataCon.

Axiom charTy : AxiomatizedTypes.Type_.

Axiom charTyCon : Core.TyCon.

Axiom charDataCon : Core.DataCon.

Axiom stringTy : AxiomatizedTypes.Type_.

Axiom stringTyCon : Core.TyCon.

Axiom intTy : AxiomatizedTypes.Type_.

Axiom intTyCon : Core.TyCon.

Axiom intDataCon : Core.DataCon.

Axiom wordTy : AxiomatizedTypes.Type_.

Axiom wordTyCon : Core.TyCon.

Axiom wordDataCon : Core.DataCon.

Axiom word8Ty : AxiomatizedTypes.Type_.

Axiom word8TyCon : Core.TyCon.

Axiom word8DataCon : Core.DataCon.

Axiom floatTy : AxiomatizedTypes.Type_.

Axiom floatTyCon : Core.TyCon.

Axiom floatDataCon : Core.DataCon.

Axiom doubleTy : AxiomatizedTypes.Type_.

Axiom doubleTyCon : Core.TyCon.

Axiom doubleDataCon : Core.DataCon.

Axiom boxingDataCon : forall {b : Type}, AxiomatizedTypes.Type_ -> BoxingInfo b.

Axiom specialBoxingDataCon_maybe : AxiomatizedTypes.Type_ ->
                                   option Core.DataCon.

Axiom boxingDataConMap : GHC.Core.Map.Type.TypeMap Core.DataCon.

Axiom boxingDataCons : list (AxiomatizedTypes.Kind * Core.DataCon)%type.

Axiom mkBoxingDataCon : Unique.Unique ->
                        (AxiomatizedTypes.Kind * FastString.FastString * FastString.FastString)%type ->
                        (AxiomatizedTypes.Kind * Core.DataCon)%type.

Axiom boolTy : AxiomatizedTypes.Type_.

Axiom boolTyCon : Core.TyCon.

Axiom falseDataCon : Core.DataCon.

Axiom trueDataCon : Core.DataCon.

Axiom falseDataConId : Core.Id.

Axiom trueDataConId : Core.Id.

Axiom orderingTyCon : Core.TyCon.

Axiom ordLTDataCon : Core.DataCon.

Axiom ordEQDataCon : Core.DataCon.

Axiom ordGTDataCon : Core.DataCon.

Axiom ordLTDataConId : Core.Id.

Axiom ordEQDataConId : Core.Id.

Axiom ordGTDataConId : Core.Id.

Axiom mkListTy : AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom listTyCon : Core.TyCon.

Axiom nilDataCon : Core.DataCon.

Axiom consDataCon : Core.DataCon.

Axiom maybeTyCon : Core.TyCon.

Axiom nothingDataCon : Core.DataCon.

Axiom justDataCon : Core.DataCon.

Axiom mkPromotedMaybeTy : AxiomatizedTypes.Kind ->
                          option AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkMaybeTy : AxiomatizedTypes.Type_ -> AxiomatizedTypes.Kind.

Axiom isPromotedMaybeTy : AxiomatizedTypes.Type_ ->
                          option (option AxiomatizedTypes.Type_).

Axiom mkTupleTy : HsSyn.Boxity ->
                  list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkTupleTy1 : HsSyn.Boxity ->
                   list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkBoxedTupleTy : list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom unitTy : AxiomatizedTypes.Type_.

Axiom mkConstraintTupleTy : list AxiomatizedTypes.Type_ ->
                            AxiomatizedTypes.Type_.

Axiom mkSumTy : list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom promotedTrueDataCon : Core.TyCon.

Axiom promotedFalseDataCon : Core.TyCon.

Axiom promotedNothingDataCon : Core.TyCon.

Axiom promotedJustDataCon : Core.TyCon.

Axiom promotedLTDataCon : Core.TyCon.

Axiom promotedEQDataCon : Core.TyCon.

Axiom promotedGTDataCon : Core.TyCon.

Axiom promotedConsDataCon : Core.TyCon.

Axiom promotedNilDataCon : Core.TyCon.

Axiom mkPromotedListTy : AxiomatizedTypes.Kind ->
                         list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom extractPromotedList : AxiomatizedTypes.Type_ ->
                            list AxiomatizedTypes.Type_.

Axiom integerTyConName : Name.Name.

Axiom integerISDataConName : Name.Name.

Axiom integerIPDataConName : Name.Name.

Axiom integerINDataConName : Name.Name.

Axiom integerTy : AxiomatizedTypes.Type_.

Axiom integerTyCon : Core.TyCon.

Axiom integerISDataCon : Core.DataCon.

Axiom integerIPDataCon : Core.DataCon.

Axiom integerINDataCon : Core.DataCon.

Axiom naturalTyConName : Name.Name.

Axiom naturalNSDataConName : Name.Name.

Axiom naturalNBDataConName : Name.Name.

Axiom naturalTy : AxiomatizedTypes.Type_.

Axiom naturalTyCon : Core.TyCon.

Axiom naturalNSDataCon : Core.DataCon.

Axiom naturalNBDataCon : Core.DataCon.

Axiom filterCTuple : PrelNames.RdrName -> PrelNames.RdrName.

Axiom pretendNameIsInScope : Name.Name -> bool.

(* External variables:
     Type bool list nat op_zt__ option AxiomatizedTypes.CType AxiomatizedTypes.Kind
     AxiomatizedTypes.PredType AxiomatizedTypes.ThetaType AxiomatizedTypes.Type_
     BasicTypes.Arity BasicTypes.TupleSort Core.Class Core.DataCon Core.Expr Core.Id
     Core.PromDataConInfo Core.RuntimeRepType Core.Scaled Core.TyCoVar Core.TyCon
     Core.TyVar Core.mkTyConTy Core.promoteDataCon FastString.FastString
     GHC.Base.String GHC.Core.Map.Type.TypeMap HsSyn.Boxity HsSyn.ConTag
     Module.Module Name.BuiltInSyntax Name.Name OccName.NameSpace OccName.OccName
     PrelNames.RdrName TcType.ConcreteTyVars UniqSet.UniqSet Unique.Unique
*)
