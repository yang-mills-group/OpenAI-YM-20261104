import YM.Integration.WilsonSeparatedOriginalResidentReadout

/-! The third signed physical coefficient on the actual original marked
residents, measured at one common intermediate state. The outer positive
posterior acts on the complete expression, including its singleton product. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalMarkedCubic
open Function Finset MeasureTheory Lattice Wilson Labels RG Source Marker Extra.Histories Push Local
open MergeProof Accent Menu RG05Readout RG05Readout.Many RG05Readout.Records RG05Readout.Address Extra.Trajectories
open WilsonSeparatedOriginalResidentReadout
open scoped Classical BigOperators
variable {G:Gauge} {I:Type} [DecidableEq I] [Fintype I] {B B':Census I}
variable (C:Family G) {N per j u:ℕ} (z:Fin 3 → I) (f:I → Goods G (C.side N per))
local notation "Y" k => C.path.rep N per k

def moment (jn:j ≤ N) (W:Config G (C.side j per)) (a:Finset (Fin 3)):ℂ:=
  actualTransport C (N:=N) (fun V => ∏ i∈a, f (z i) V) jn W

def cubic (a:Finset (Fin 3) → ℂ):ℂ:=
  a univ - (a {0,1}*a {2}+a {0,2}*a {1}+a {1,2}*a {0}) + 2*(a {0}*a {1}*a {2})

def pair (a:Finset (Fin 3) → ℂ)(i k:Fin 3):ℂ:=a {i,k} - a {i}*a {k}

def settled (a:Finset (Fin 3) → ℂ)(c:Fin 3 → ℂ):ℂ:=
  cubic a + pair a 0 1*(a {2}-c 2) + pair a 0 2*(a {1}-c 1) + pair a 1 2*(a {0}-c 0) + ∏ i:Fin 3, (a {i}-c i)

/-- All seven physical moments and the quiet component use the same normalized
positive Wilson conditional that supplies the original unnormalized birth. -/
theorem component (different:Injective z)(all:univ.image z∈B'.choices)(inc:B'.choices⊆B.choices)
    (paid:Integrable (birth B (Y N) f) (prior G _))(jn:j ≤ N)(W:Config G (C.side j per))(a:Finset (Fin 3)):
    (((Y j).eval W:ℂ)⁻¹)*(narrow inc (gust C.path N per N (birth B (Y N) f) j jn W)).part (modes z all a)=
      moment C z f jn W a:=by
  let m:=route inc (modes z all a)
  have born:(fun V => (birth B (Y N) f V).part m)=fun V => ((Y N).eval V:ℂ)*(∏ i∈a, f (z i) V):=by
    funext V;unfold birth Mach;rw [Poly.part_smul,pass_fire]
    change ((Y N).eval V:ℂ)*(∏i∈a.image z, f i V)=_
    rw [Finset.prod_image different.injOn]
  rw [narrow_right]
  have observed:=congrFun (pushpart jn (birth B (Y N) f) m paid) W
  rw [show (gust C.path N per N (birth B (Y N) f) j jn W).part (route inc (modes z all a))=_ from observed,born]
  simp only [moment,actualTransport,Complex.real_smul,Complex.ofReal_inv]

omit [Fintype I] [DecidableEq I] in
private lemma normalized (made:C.Makes)(jn:j ≤ N)(W:Config G (C.side j per)):
    moment C z f jn W ∅=1:=by
  simp only [moment,Finset.prod_empty]
  exact actualTransport_const C made (le_refl N) (1:ℂ) jn W

/-- This equation is pointwise on every true old group field, including rough
ones, before invoking any estimate for the jointly measured terms. -/
theorem physical (made:C.Makes)(different:Injective z)(all:univ.image z∈B'.choices)(inc:B'.choices⊆B.choices)
    (paid:Integrable (birth B (Y N) f) (prior G _))(jn:j ≤ N)(W:Config G (C.side j per))(c:Fin 3 → ℂ):
    actualTransport C (N:=N) (fun V => ∏ i:Fin 3, (f (z i) V-c i)) jn W=settled (moment C z f jn W) c:=by
  rw [WilsonSeparatedOriginalResidentReadout.reported C z different all inc f c paid jn W,WilsonSeparatedOriginalResidentReadout.read]
  let a:=moment C z f jn W
  let x:=narrow inc (gust C.path N per N (birth B (Y N) f) j jn W)
  let cost:=((Y j).eval W:ℂ)⁻¹
  have one(a':Finset (Fin 3)):cost*x.part (modes z all a')=a a':=component C z f different all inc paid jn W a'
  change cost*alternatives c (fun t=>x.part (modes z all t))=settled a c
  calc
    _ = alternatives c (fun t => cost*x.part (modes z all t)):=by unfold alternatives;ring
    _ = alternatives c a:=congrArg (alternatives c) (funext one)
    _ = settled a c:=by
      have n:a ∅=1:=normalized C z f made jn W
      simp only [settled,cubic,pair,alternatives,Fin.prod_univ_three,n];ring

/-- A single real earlier Wilson posterior sees the mixed conditional terms
and the full product of its three later issued singleton deviations. -/
theorem original (made:C.Makes)(different:Injective z)(all:univ.image z∈B'.choices)(inc:B'.choices⊆B.choices)
    (paid:Integrable (birth B (Y N) f) (prior G _))(jn:j ≤ N)(uj:u ≤ j)(U:Config G (C.side u per)):
    let c:=fun i => actualTransport C (N:=N) (f (z i)) (uj.trans jn) U
    actualTransport C (N:=N) (fun V => ∏ i:Fin 3, (f (z i) V-c i)) (uj.trans jn) U=
      actualTransport C (N:=N) (fun W => settled (moment C z f jn W) c) uj U:=by
  intro c
  rw [←actualTransport_tower C made (le_refl N) (fun V => ∏ i:Fin 3, (f (z i) V-c i)) jn uj]
  exact congrArg (fun H => actualTransport C (N:=N) H uj U) (funext fun W => physical C z f made different all inc paid jn W c)

end YM.Integration.WilsonSeparatedOriginalMarkedCubic
