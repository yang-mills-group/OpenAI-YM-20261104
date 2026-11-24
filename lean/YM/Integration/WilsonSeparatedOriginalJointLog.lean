import YM.Comparison.RG02.Cumulants.Parents
import YM.Integration.WilsonSeparatedOriginalMarkedCubic

/-! The measured signed third coefficient is the intrinsic connected entry
of the same normalized RG05 marked polynomial on its admitted resident set. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalJointLog
open Function Finset MeasureTheory Lattice Wilson RG Source Marker Multi Extra.Histories Push Local
open MergeProof Accent Menu RG05Readout RG05Readout.Many RG05Readout.Records RG05Readout.Address
open Extra.Trajectories Primitives.GCC.Anchor Comparison.RG02.Cumulants
open WilsonSeparatedOriginalMarkedCubic WilsonSeparatedOriginalResidentReadout
open scoped Classical BigOperators

abbrev three : Census (Fin 3):=⟨univ,mem_univ _,fun _=>mem_univ _,fun _ _ _=>mem_univ _⟩
def shape (a:Finset (Fin 3)):three.Mode:=⟨a,mem_univ _⟩
private def slate : Finset three.Mode:={shape {0},shape {0,1},shape {0,2},shape univ}

private theorem contains (a:three.Mode):a∈slate ↔ (0:Fin 3)∈a.val:=by
  simp only [slate,mem_insert,mem_singleton]
  constructor
  · rintro (rfl|rfl|rfl|rfl) <;> simp [shape]
  · intro h0
    by_cases h1:(1:Fin 3)∈a.val <;> by_cases h2:(2:Fin 3)∈a.val
    · right;right;right;apply Subtype.ext;ext i;fin_cases i <;> simp [shape,h0,h1,h2]
    · right;left;apply Subtype.ext;ext i;fin_cases i <;> simp [shape,h0,h1,h2]
    · right;right;left;apply Subtype.ext;ext i;fin_cases i <;> simp [shape,h0,h1,h2]
    · left;apply Subtype.ext;ext i;fin_cases i <;> simp [shape,h0,h1,h2]

private theorem avoid:shape {0} ∉ ({shape {0,1},shape {0,2},shape univ}:Finset three.Mode) ∧
    shape {0,1} ∉ ({shape {0,2},shape univ}:Finset three.Mode) ∧ shape {0,2} ∉ ({shape univ}:Finset three.Mode):=by
  have eqv(a b:Finset (Fin 3)):shape a=shape b ↔ a=b:=⟨fun h=>congrArg Subtype.val h,congrArg shape⟩
  simp only [mem_insert,mem_singleton,eqv];decide

private theorem root (P:Poly three)(hp:P.part three.quiet=1):
    P.part (shape univ)=∑a∈slate,(connected P).part a*P.part (diff (shape univ) a.val):=by
  let s:=shape univ
  have hi:(0:Fin 3)∈s.val:=mem_univ _
  have eqn:=moment_root 0 P hp
  rw [mul_comm,←Poly.studs (highlight 0 (connected P))] at eqn
  have h:=(highlight_part 0 P s).trans (if_pos hi)
  rw [←h,eqn,sum_mul,Poly.part_sum]
  have live:(univ.filter fun a:three.Mode=>a.val⊆s.val ∧ (0:Fin 3)∈a.val)=slate:=by
    ext a;simp only [Finset.mem_filter,mem_univ,true_and,contains];exact and_iff_right (subset_univ _)
  rw [←live,Finset.sum_filter]
  apply sum_congr rfl;intro a _
  simp only [mul_at_part,highlight_part];by_cases h0:(0:Fin 3)∈a.val <;> simp [h0,ite_self,s]

/-- The equality holds for the actual input source logarithm, including any
other names in its census. Only its restriction to these three names is read. -/
theorem three_fields (P:Poly three)(hp:P.part three.quiet=1):
    (connected P).part (shape univ)=cubic (fun a=>P.part (shape a)):=by
  have eqn:=root P hp
  rw [slate,Finset.sum_insert avoid.1,Finset.sum_insert avoid.2.1,Finset.sum_insert avoid.2.2,Finset.sum_singleton] at eqn
  have lost (a b:Finset (Fin 3))(e:(univ:Finset (Fin 3))\a=b):diff (shape univ) (shape a).val=shape b:=Subtype.ext e
  rw [lost {0} {1,2} (by decide),lost {0,1} {2} (by decide),lost {0,2} {1} (by decide),lost univ ∅ sdiff_self] at eqn
  have quiet:P.part (shape ∅)=1:=hp
  have one:(connected P).part (shape {0})=P.part (shape {0}):=lamp 0 P hp
  have two(i j:Fin 3)(different:i≠j):(connected P).part (shape {i,j})=P.part (shape {i,j})-P.part (shape {i})*P.part (shape {j}):=twins i j (shape {i,j}) P hp different rfl
  rw [quiet,mul_one,one,two 0 1 (by decide),two 0 2 (by decide)] at eqn
  unfold cubic;linear_combination -eqn

variable {G:Gauge} {I:Type} [DecidableEq I] [Fintype I] {B B':Census I}
variable (C:Family G) {N per j:ℕ} (z:Fin 3 → I) (f:I → Goods G (C.side N per))
local notation "Y" k => C.path.rep N per k

/-- The numerical recipient of the original spatially charged complete mixed
density. Every component is evaluated on the same physical vacuum. -/
theorem measured (made:C.Makes)(different:Injective z)(all:univ.image z∈B'.choices)(inc:B'.choices⊆B.choices)
    (paid:Integrable (birth B (Y N) f) (prior G _))(jn:j ≤ N)(W:Config G (C.side j per)):
    let raw:=((Y j).eval W:ℂ)⁻¹ • narrow inc (gust C.path N per N (birth B (Y N) f) j jn W)
    cubic (moment C z f jn W)=(connected raw).part (modes z all univ):=by
  intro raw
  let names:Names three B':={e:=⟨z,different⟩,visible:=fun a=> B'.down all _ (Finset.image_mono z (Finset.subset_univ a.val))}
  let p:=names.restriction raw
  have sent (a:Finset (Fin 3)):p.part (shape a)=moment C z f jn W a:=by
    change ((Y j).eval W:ℂ)⁻¹*(narrow inc (gust C.path N per N (birth B (Y N) f) j jn W)).part (modes z all a)=_
    exact component C z f different all inc paid jn W a
  have quiet:p.part three.quiet=1:=by
    rw [show three.quiet=shape ∅ from rfl,sent];simp only [WilsonSeparatedOriginalMarkedCubic.moment,Finset.prod_empty]
    exact actualTransport_const C made (le_refl N) (1:ℂ) jn W
  have pristine:raw.part B'.quiet=1:=by change raw.part (names.share three.quiet)=1 at quiet;simpa only [Names.quiet] using quiet
  have reindexed:=congrArg (fun H:Poly three=>H.part (shape univ)) (names.connected_restrict pristine)
  exact ((congrArg cubic (funext sent)).symm.trans (three_fields p quiet).symm).trans reindexed.symm

end YM.Integration.WilsonSeparatedOriginalJointLog
