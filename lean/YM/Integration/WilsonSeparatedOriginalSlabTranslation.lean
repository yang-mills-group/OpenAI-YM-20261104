import YM.Integration.WilsonPositionSeparatedProfileCenteredBranch
import YM.Integration.WilsonSeparatedOriginalProfileAnchor
import YM.Integration.WilsonSeparatedOriginalSlabFold

/-! A common true subcell displacement translates all original Wilson clinic fields on every microscopic gauge. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabTranslation
open Function Finset Lattice Wilson RG Source RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Records
open Push MergeProof Ribbons PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}(C:Family G){n N per:ℕ}

theorem clinic (top:n ≤ N)(d:ℕ)(v:Palette C d)(o c:Site (C.side n per))(f:Body)(U:Config G (C.side N per)):
    Records.clinic C per N d v n o (1,false) f (pull 1 ((C.S.toDepth top per).embed c) U)=
      Records.clinic C per N d v n (o+c) (1,false) f U:=by
  let A:=C.S.toDepth top per
  have add:(C.S.toDepth top per).embed o+(C.S.toDepth top per).embed c=(C.S.toDepth top per).embed (o+c):=(map_add A.root o c).symm
  simp only [Records.clinic,Records.uniform,dif_pos top,stepUp,pull_pull,mul_one,affine]
  have one:(1:Signed).act (A.embed o)=A.embed o:=by simp
  rw [show (1:Signed).act ((C.S.toDepth (top.trans le_rfl) per).embed o)=(C.S.toDepth top per).embed o from one,add]

theorem word {I:Type*}[Fintype I](top:n ≤ N)(d:I → ℕ)(v:(i:I) → Palette C (d i))(o:I → Site (C.side n per))
    (c:Site (C.side n per))(f:I → Body)(U:Config G (C.side N per)):
    (∏i,Records.clinic C per N (d i) (v i) n (o i) (1,false) (f i) (pull 1 ((C.S.toDepth top per).embed c) U))=
      ∏i,Records.clinic C per N (d i) (v i) n (o i+c) (1,false) (f i) U:=by
  apply prod_congr rfl;intro i _;exact clinic C top (d i) (v i) (o i) c (f i) U

end YM.Integration.WilsonSeparatedOriginalSlabTranslation
