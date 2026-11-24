import YM.Integration.WilsonThermometerOccupiedLinear

/-! Finite source withdrawals commute with the entire original blocked Wilson integral. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedTransport
open Function Filter Finset MeasureTheory Lattice RG Wilson Labels Source Work.G08 Next.Foundations
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Legato RG16 WilsonThermometerUnitFilingCoarse
open Marker WilsonThermometerOccupiedInterpolation
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N p b j:ℕ}
local notation "H" => R.family.path
local notation "X" => Config G (R.family.side b p)
private theorem plus (f g:X→ℂ) (hf:Integrable f (prior G _))(hg:Integrable g (prior G _))(jb:j≤b):
    gust H N p b (f+g) j jb=gust H N p b f j jb+gust H N p b g j jb:=by
  induction jb using Nat.decreasingInduction with
  | self=>rw [gust_base,gust_base,gust_base]
  | of_succ i ix ih=>
    rw [gust_step H N p b _ ix,ih,StepData.push_add ((H).levels.transition_mass ..) _ _
      (gust_live H N p b f hf ix) (gust_live H N p b g hg ix),
      ←gust_step H N p b f ix,←gust_step H N p b g ix]

private theorem scale (c:ℂ) (f:X→ℂ)(hf:Integrable f (prior G _))(jb:j≤b):
    gust H N p b (c • f) j jb=c • gust H N p b f j jb:=by
  induction jb using Nat.decreasingInduction with
  | self=>rw [gust_base,gust_base]
  | of_succ i ix ih=>
    rw [gust_step H N p b _ ix,ih,StepData.push_smul _ _ _ _ (gust_live H N p b f hf ix),
      ←gust_step H N p b f ix]

private theorem summed {V:Type*} (s:Finset V)(a:V→ℂ)(f:V→X→ℂ)
    (live:∀v,Integrable (f v) (prior G _))(jb:j≤b):
    Integrable (∑i∈s,a i • f i) (prior G _) ∧
    gust H N p b (∑i∈s,a i • f i) j jb=∑i∈s,a i • gust H N p b (f i) j jb:=by
  induction s using Finset.induction_on with
  | empty=>
    simp only [sum_empty]
    have z:=scale R (N:=N) 0 (0:X→ℂ) (integrable_zero ..) jb
    exact ⟨integrable_zero ..,by simpa only [zero_smul] using z⟩
  | @insert v t hv ih=>
    simp only [sum_insert hv]
    have sc:=(live v).smul (a v)
    exact ⟨sc.add ih.1,by rw [plus R _ _ sc ih.1 jb,scale R _ _ (live v) jb,ih.2]⟩

variable {V:Type} [DecidableEq V] {marks:Census V}

theorem projected (F:X→Poly marks)(paid:Integrable F (prior G _))(s:marks.Mode){j:ℕ}(jb:j ≤ b):
    (fun W=>(gust H N p b F j jb W).part s)=gust H N p b (fun U=>(F U).part s) j jb:=by
  induction jb using Nat.decreasingInduction with
  | self=>rw [gust_base,gust_base]
  | of_succ j jt ih=>
    rw [gust_step H N p b F jt,gust_step H N p b _ jt]
    have pass:=push_get ((H).levels.transition_mass j p ((H).β N p (j+1)))
      (gust_live H N p b F paid jt) s
    exact pass.trans (congrArg (((H).levels.clock.op j p).push ((H).β N p (j+1))) ih)



theorem original {N p b j:ℕ} {I:Type} [Fintype I]
    (F M:Config G (R.family.side b p)→Poly marks) (taps:I → Config G (R.family.side b p)→Poly marks) (w:I→ℂ)
    (s:marks.Mode) (jb:j ≤ b) (hF:Integrable F (prior G _)) (hM:Integrable M (prior G _))
    (inputs:∀i,Integrable (taps i) (prior G _))
    (upper:∀U,(F U).part s-(M U).part s=∑i,w i*((taps i U).part s)) (W:Config G (R.family.side j p)):
    (gust H N p b F j jb W).part s - (gust H N p b M j jb W).part s =
    ∑i,w i*(gust H N p b (taps i) j jb W).part s:=by
  let f:=fun i U=>(taps i U).part s
  let m:=fun U=>(M U).part s
  have pay:=summed R (N:=N) univ w f (fun i=>(Poly.get s).integrable_comp (inputs i)) jb
  have top:(fun U=>(F U).part s)=m+∑i,w i • f i:=by
    funext U
    have h:=upper U
    simp only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,m,f]
    linear_combination h
  have eq:=congrFun (projected R (N:=N) F hF s jb) W
  rw [top,plus R m _ ((Poly.get s).integrable_comp hM) pay.1 jb,pay.2] at eq
  have old:=congrFun (projected R (N:=N) M hM s jb) W
  have point (i:I): gust H N p b (f i) j jb W=(gust H N p b (taps i) j jb W).part s:=
    (congrFun (projected R (N:=N) (taps i) (inputs i) s jb) W).symm
  change (gust H N p b F j jb W).part s=(gust H N p b m j jb+∑i,w i • gust H N p b (f i) j jb) W at eq
  simp only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,point] at eq
  change (gust H N p b M j jb W).part s=gust H N p b m j jb W at old
  rw [eq,old]
  ring

end YM.Integration.WilsonOriginalOccupiedTransport
