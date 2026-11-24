import YM.Integration.WilsonPhysicalPositionMixedRead
import YM.Integration.WilsonPhysicalPositionBornInner

/-! A reflected measurement of the electable real column in the two actual
physical frames. Every Born limit is the native positive signed-axis form
of the corresponding field displacement. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionDirectedReturn
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open PertExtension.Rigidity.Positive
open WilsonPhysicalPositionAdmissible (Native)
open scoped Topology Classical BigOperators
open WilsonPhysicalPositionReflectedReturn (ports sites clear)
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

def cross {d:ℕ}(v:D d)(r t:ℝ):ℝ:=
  ∑s:Signed, (WilsonPhysicalPositionMixedRead.value F J (fun j:Fin 2=>decide (j=0)) (ports v s) sites r t).re

private def pair {d:ℕ}(x y:D d)(s:Signed):Fin 2→D d:=
  let U:=(Bel C.book).mirror (spin_free C.labels) d s
  ![U y,(Bel C.book).adj (spin_free C.labels) d 0 (U x)]

private theorem gram_eq {d:ℕ}(x y:D d)(s:Signed):
    (WickGoal (C:=C) (d:=fun _:Fin 2=>d) (pair x y s) sites).re=
      gram C.labels (hierarchy C.labels) 0 (transform C.labels (hierarchy C.labels) s x)
        (transform C.labels (hierarchy C.labels) s y):=by
  let T:=Bel C.book
  let U:=T.mirror (spin_free C.labels) d s
  change _=(gramC C.labels (hierarchy C.labels) 0 (U x) (U y)).re
  rw [gramC_apply]
  apply congrArg Complex.re
  change T.useAt T sites (fun i:Fin 2=>(⟨d,pair x y s i⟩:T.Tag))=T.useAt T sites _
  apply congrArg (T.useAt T sites)
  funext i
  fin_cases i <;> rfl

private theorem polar {d:ℕ}(Z:D d→ₗ[ℂ]D d)(h:Native C Z)(v:D d)(s:Signed):
    ((fun j:Fin 2=>if decide (j=0) then ports v s j else Z (ports v s j))=pair (Z v) v s) ∧
    ((fun j:Fin 2=>Z (ports v s j))=pair (Z v) (Z v) s):=by
  let T:=Bel C.book
  let U:=T.mirror (spin_free C.labels) d s
  let A:=T.adj (spin_free C.labels) d 0
  have flip(w:D d):Z (A w)=A (Z w):=by
    change Z (WilsonPhysicalPositionAdmissible.turns C d (Signed.mirror 0) (WilsonPhysicalPositionAdmissible.real C d w))=_
    rw [h.orientation,h.conjugate]
    rfl
  have last:Z (A (U v))=A (U (Z v)):= (flip _).trans (congrArg (fun b=>A b) (h.orientation s v))
  constructor
  · funext j
    fin_cases j
    · rfl
    · exact last
  · funext j
    fin_cases j
    · exact h.orientation s v
    · exact last

private theorem admissible (lead:Leading F J){I:Type*}{l:Filter I}[NeBot l]{r t:I→ℝ}
    (hr:Tendsto r l trail){u:ℝ}(ht:Tendsto t l (𝓝 u))(pos:∀i,0<t i)
    {d:ℕ}(Z:D d→ₗ[ℂ]D d)
    (conv:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v))):Native C Z:=by
  have hrt:Tendsto (fun i=>t i*r i) l trail:=by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [mul_zero] using ht.mul (hr.mono_right nhdsWithin_le_nhds)
    filter_upwards [hr.eventually self_mem_nhdsWithin] with i hi using mul_pos (pos i) hi
  apply WilsonPhysicalPositionBranchLimits.closed (Y:=fun i=>(Frame.cocycle d J (r i) (t i) (pos i)).toLinearMap) _ conv
  filter_upwards [hr.eventually (WilsonPhysicalPositionCocycleNative.purchased F J lead d),
    hrt.eventually (WilsonPhysicalPositionCocycleNative.purchased F J lead d)] with i qr qv
  exact WilsonPhysicalPositionCocycleNative.original F J (pos i) qr qv

theorem original (lead:Leading F J){I:Type*}{l:Filter I}[NeBot l]{r t:I→ℝ}
    (hr:Tendsto r l trail){u:ℝ}(hu:0<u)(ht:Tendsto t l (𝓝 u))(pos:∀i,0<t i)
    {d:ℕ}(Z:D d→ₗ[ℂ]D d)
    (conv:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v)))(v:D d):
    Tendsto (fun i=>cross F J v (r i) (t i)) l (𝓝 (positive C.labels (hierarchy C.labels) (Z v) v)) ∧
      positive C.labels (hierarchy C.labels) (Z v) (Z v)=positive C.labels (hierarchy C.labels) v v:=by
  have h:=admissible F J lead hr ht pos Z conv
  unfold cross positive
  simp only [LinearMap.sum_apply,LinearMap.BilinForm.comp_apply]
  constructor
  · apply tendsto_finsetSum Finset.univ
    intro s _
    have paid:=WilsonPhysicalPositionMixedRead.limit F J lead hr hu ht pos Z conv
      (fun j:Fin 2=>decide (j=0)) (ports v s) clear
    rw [(polar Z h v s).1] at paid
    rw [←gram_eq (Z v) v s]
    exact Complex.continuous_re.continuousAt.tendsto.comp paid
  · apply Finset.sum_congr rfl
    intro s _
    have eq:=WilsonPhysicalPositionBornTransition.invariant F J lead hr hu ht pos Z conv (ports v s) clear
    rw [(polar Z h v s).2] at eq
    rw [←gram_eq (Z v) (Z v) s,←gram_eq v v s]
    exact congrArg Complex.re eq

end YM.Integration.WilsonPhysicalPositionDirectedReturn
end
