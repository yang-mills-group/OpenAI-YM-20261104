import YM.FVA2.Notch.Cover
/-!
# Two-cutoff bound on `Flight`s

At fixed arity, setup `Flight` (see `Cover.lean`) allows arbitrary fixed angular margin.
The leading chip is a single positive power of spacing. This is **before** requiring schedules
with a rate of growth of the volume. As specified in `mesh_gain`, the estimate is eventual
in inverse spacing, and we need at least a minimal side (in lattice units). If you want actual
convergence for the second term too make sure to take sufficient growth, e.g. `Pitch`/`Main`
use the `Front` filter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Notch.Flight
open Function Filter Set Finset Metric MeasureTheory Real Lattice MS MS.High
open MS.Book MS.Book.Convolve MS.Tone MS.Tide MS.Rake MS.Land MS.Dial MS.Orbit MS.City MS.Latch MS.Latch.Job MS.Fleet MS.Vista MS.Vane MS.Book.Program MS.Puff MS.Puff.Mom MS.Book
open Wilson Further XSpace.Cirrus Arrival Arrival.Landing Arrival.Schedule Removal Press
open scoped Topology ContDiff BigOperators Classical
variable {n:ℕ}{G:Gauge}(Y:XSpace.Initialize G)(u:Fin n→Label (Press.portDeck G))(M:Land.Prescription (Press.portDeck G))
local notation "B"=> Press.portDeck G
local notation "U"=> Fin n
local notation "Z"=> XSpace.Cirrus.Sample n
local notation "Ψ"=> XSpace.Cirrus.grab (n:=n)
variable (p:XSpace.Cirrus.Sample n)(μ:ℝ)
-- literal period even and ≥4. Use inside `Birth` via XSpace's gauge-at-any-period.
lemma recenter (c:U→ Cover)(f:U→ Cover)(A:Cover)(C:Cover) (s:Finset (Fin n)) (H:∀ w:U,wrap p.F.p.side (A+c w)=wrap p.F.p.side (C+f w)): Top.value Y u M A c p.F.p.side μ s=Top.value Y u M C f p.F.p.side μ s:= by
 let T:= p.F.p.standardTree; unfold Top.value; apply congr_arg; funext l; congr 2; apply PowerSeries.map_injective Complex.ofRealHom Complex.ofReal_injective; rw [← Birth.accord (T:=T), ← Birth.accord (T:=T)]; simp_rw [List.map_map]; rw [show Birth.entered Y T ∘ Top.declares u A c=Birth.entered Y T ∘ Top.declares u C f from ?_]; funext j; simp [Birth.entered,Top.declares,H]; rfl
omit p
variable (s:Finset (Fin n))(k:ℕ) {r:ℝ}{K: Set (Points n)} (i:Flight r K)
local notation "P"=> trail r K μ
local notation "I"=> Flight r K
local notation "E"=> entries μ Y u M s k
open PeakT (ordZ)
private lemma ticket (m:ℕ): MS.Tide.higher (trail r K μ).profile m i=((i.sample.F.spacing:ℂ)^m)⁻¹:= by
 let a:= theta i.sample.F; let x:=i.sample.F.spacing; let h : exp (-a)=x:= bornS (signs i).2.2.1; rw [Real.exp_neg] at h; change _=( ( (x:ℝ):ℂ )^_ )⁻¹; rw [←h]; unfold higher Port.τ; simp only [ inv_pow,inv_inv,zpow_natCast,Complex.ofReal_inv ]; exact Complex.ofReal_pow ..
variable {O:Booked (Press.portDeck G)}(T:MS_Data G O){f z:Terrify (Fin n) (Flight r K)}{l:Filter (Flight r K)}
local notation "Ξ"=> MenuCost T Y (trail r K μ) M u μ l f z
lemma arranges (H:MenuCost T Y (trail r K μ) M u μ l f z): MS.Tide.fare ( MS.Rake.Label.h ∘ u ) (trail r K μ).profile ( ordZ f ) s k i= E i.sample:= by
 let p:=i.sample; let aH :=μ-theta p.F; let N:= psi p.F; let d:= Vane.charge (Label.h∘u) s; let x:=(P).head i; let b a:=(P).off a i; obtain hL:= H.contact i s
 have hQ(w:Fin n): wrap p.F.p.side (x+b w)= wrap p.F.p.side ( 0+p.layout w ):= by
    rw [map_add,zero_add, ← psi_back p.F ]; rw [show wrap (periodN (psi p.F)) x=wrap (periodN (psi p.F)) i.peg from wrap_lift _ ]; change wrap (periodN (psi p.F)) i.peg+ wrap (periodN (psi p.F)) (p.layout w-i.peg)=_; rw [map_sub]; abel
 change higher ( trail r K μ ).profile _ i * _= ((p.F.spacing:ℂ)^_)⁻¹*_; rw [show ordZ _ _ _ _=Top.value _ u M x b (periodN (psi p.F)) aH s k from congr_fun hL k, psi_back p.F,recenter Y u M p aH b p.layout x 0 s hQ,ticket μ]; -- field notation
variable (g:G.Simple)(hS:TaylorOKF T ( wickInput Y ) M) (hc:IsCompact K)(ht:K⊆ conf n)(hr:0<r)
local notation "D"=> Landing.moondye μ T u s k
include ht
lemma in_space (v:Points n)(hx:v∈K)(hp:familiar i.sample=v): tour T u μ ( testP (trail r K μ) i )=tour T u μ (plot v):= by
 subst v; unfold tour book; rw [transfers μ u T (x:=plot _) (track (ht hx)) (fun u w=>(symbol i μ u w).symm)]
include hS g hc hr ht
/-- Two-rate removed arrays BEFORE pos normalization. No choice of any pole generator
 here after choosing a fixed volume. Estimate is eventual in inverse spacing. `Total.hard`
 used here. -/
lemma mapCost : Total ( comap (fun i:Flight r K=> theta i.sample.F) atTop ) (trail r K μ).profile (trail r K μ).side (fun i=> entries μ Y u M s k i.sample- D (familiar i.sample)):= by
 obtain ⟨f,z,hp⟩:= tabulate_ge T Y (trail r K μ) M u (worthy hc hr ht μ) (l:=comap (P).profile.θ atTop) tendsto_comap hS g
 convert (hp.reaches s k).2.1.2 using 1
 · rfl
 funext i; change E i.sample -_=fare (Label.h∘u) (P).profile (ordZ f) s k i-tour T u μ (testP (P) i) s k; rw [arranges Y u M μ s k i T hp,in_space u μ i T ht (familiar i.sample ) (signs i|>.2.1) rfl ]; rfl
lemma mesh_gain : ∃ (C:ℝ) (m:ℕ) (d:ℝ),0<C ∧ ∀ i: Sample n,Entry r i→ familiar i∈K→ 16 ≤ i.F.p.side.val → i.F.spacing≤1 → d≤ - log i.F.spacing → ‖entries μ Y u M s k i-D (familiar i)‖≤ C*( Speed.chip i.F+ ( i.F.spacing ^ m )⁻¹*i.F.size^(-mildG) ):= by
 obtain ⟨C,hC,m,H⟩:= ( mapCost Y u M μ s k T g hS hc ht hr ).hard; rw [eventually_comap] at H; obtain ⟨d,H⟩:= eventually_atTop.mp H; refine ⟨ C,m,d,hC,fun i hi hx hA hL hh=>?_ ⟩; let y:Flight r K:= ⟨i,hi,hx,hL,hA⟩; rw [← theta_value hL] at hh; apply ( H (theta i.F) hh y rfl ).trans_eq; rw [ show exp (-(P).profile.θ y)=i.F.spacing from bornS hL,show phys (P).profile (P).side y=i.F.size from ?_ ]
 unfold phys; change exp (-theta i.F) * ( ( periodN (psi i.F) ).val:ℝ )=_; rw [ show exp _=i.F.spacing from bornS hL, psi_back i.F ]; rfl
end YM.FVA2.Notch.Flight
