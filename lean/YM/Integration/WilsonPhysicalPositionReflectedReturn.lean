import YM.Integration.WilsonPhysicalPositionTwoHomeObservable

/-! A reflected measurement of the electable real column in the two actual
physical frames. Every Born limit is the native positive signed-axis form
of the corresponding field displacement. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionReflectedReturn
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open PertExtension.Rigidity.Positive
open WilsonPhysicalPositionAdmissible (Native)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

def ports {d:ℕ}(v:D d)(s:Signed):Fin 2→D d:=
  let w:=(Bel C.book).mirror (spin_free C.labels) d s v
  ![w,(Bel C.book).adj (spin_free C.labels) d 0 w]

def sites:=Extra.FD.couple (_root_.YM.basis 0) 0

theorem clear:sites∈conf 2:=by
  apply Extra.FD.couple_ok
  intro e
  exact one_ne_zero (by simpa only [basis_norm,norm_zero] using congrArg norm e)

def reading {d:ℕ}(v:D d)(r t:ℝ):ℝ:=
  ∑s:Signed, (WilsonPhysicalPositionTwoHomeObservable.heard F J (ports v s) sites r t).re

private theorem gram_eq {d:ℕ}(v:D d)(s:Signed):
    (WickGoal (C:=C) (d:=fun _:Fin 2=>d) (ports v s) sites).re=
      gram C.labels (hierarchy C.labels) 0 (transform C.labels (hierarchy C.labels) s v)
        (transform C.labels (hierarchy C.labels) s v):=by
  let T:=Bel C.book
  let w:=T.mirror (spin_free C.labels) d s v
  change _=(gramC C.labels (hierarchy C.labels) 0 w w).re
  rw [gramC_apply]
  apply congrArg Complex.re
  change T.useAt T sites (fun i:Fin 2=>(⟨d,ports v s i⟩:T.Tag))=T.useAt T sites _
  apply congrArg (T.useAt T sites)
  funext i
  fin_cases i <;> rfl

private theorem ports_sub {d:ℕ}(Z:D d→ₗ[ℂ]D d)(h:Native C Z)(s:Signed)(v:D d):
    (fun j=>ports v s j-Z (ports v s j))=ports (v-Z v) s:=by
  let T:=Bel C.book
  let U:=T.mirror (spin_free C.labels) d s
  let A:=T.adj (spin_free C.labels) d 0
  have comm(v:D d):Z (A v)=A (Z v):=by
    change Z (WilsonPhysicalPositionAdmissible.turns C d (Signed.mirror 0) (WilsonPhysicalPositionAdmissible.real C d v))=_
    rw [h.orientation,h.conjugate]
    rfl
  funext j
  fin_cases j
  · change U v-Z (U v)=U (v-Z v)
    exact (congrArg (fun w=>U v-w) (h.orientation s v)).trans (U.map_sub v (Z v)).symm
  change A (U v)-Z (A (U v))=A (U (v-Z v))
  rw [comm,U.map_sub,A.map_sub]
  exact congrArg (fun w=>A (U v)-A w) (h.orientation s v)

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
    Tendsto (fun i=>reading F J v (r i) (t i)) l
      (𝓝 (positive C.labels (hierarchy C.labels) (v-Z v) (v-Z v))):=by
  have good:=admissible F J lead hr ht pos Z conv
  have part(s:Signed):Tendsto (fun i=>(WilsonPhysicalPositionTwoHomeObservable.heard F J (ports v s) sites (r i) (t i)).re) l
      (𝓝 (gram C.labels (hierarchy C.labels) 0 (transform C.labels (hierarchy C.labels) s (v-Z v))
          (transform C.labels (hierarchy C.labels) s (v-Z v)))):=by
    have q:=WilsonPhysicalPositionTwoHomeObservable.limit F J lead hr hu ht pos Z conv (ports v s) clear
    rw [ports_sub Z good s v] at q
    have qr:=Complex.continuous_re.continuousAt.tendsto.comp q
    rw [←gram_eq (v-Z v) s]
    exact qr
  unfold reading positive
  simp only [LinearMap.sum_apply,LinearMap.BilinForm.comp_apply]
  exact tendsto_finsetSum Finset.univ fun s _=>part s

end YM.Integration.WilsonPhysicalPositionReflectedReturn
end
