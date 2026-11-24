import YM.LocalLTE.Fan.Chair
/-! Quantities at the Σ staple of acquisitions. Keep point Quell uniform tags. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan.Field
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel Bakers PhysicalNext.Repeat Greenbelt Blaze.Stained
variable {v z r W w s t y η γ B a μ b C C' q X Y : ℝ} {j n k m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}{χ:Chi}
variable (D: Finset (Veil c f)) (H: Cash W t μ L Q o a T R)
variable (K: Captain H j C v z r Y C' w B q m χ)
section
variable {ι ι' : Type}[Fintype ι]
lemma avgBound [Nonempty ι](f:ι→ℝ)(h:∀ i,‖f i‖≤W) : ‖likely f‖≤W:= by
  let C:ℝ:=Fintype.card ι; have hC:0 < C:=by unfold C; positivity
  unfold likely; rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hC.le)]
  exact (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=> h i))) (inv_nonneg.mpr hC.le)).trans_eq (by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul, inv_mul_cancel_left₀ hC.ne'])
lemma difference [Nonempty ι] (f g:ι→ℝ)(h:∀ i,‖f i-g i‖≤W): ‖likely f-likely g‖≤ W:= by
   have hx : likely f-likely g=likely (fun i=>f i-g i):= by unfold likely; rw [Finset.sum_sub_distrib,mul_sub]
   rw [hx]; exact avgBound _ h
lemma questv [Fintype ι'](f:ι→ι'→ℝ):∑ i,likely (fun j=> f j i) = likely (fun j=> ∑ i,f j i):= by unfold likely; rw [← Finset.mul_sum,Finset.sum_comm]
end
variable (x: Directions G c)(p:Disk G c)(hP:p=(gStep R.beta,x))(hp:flags (Pressure.temp t) (increment (1: Config G c) x)=∅)(hT:Stamp T)
variable (β K₀:ℝ)(hB:1≤ β)(z':ℕ→ℕ)(A:Veil c f→ℝ)
local notation "d"=> postponement L t o
-- Ω invoice
section
local notation "ℋ"=> (2+Real.exp 1)
local notation "Z"=> (∏ i∈D,A i)
variable (hA:∀ (F: Forest S.ratio)(X:Coat T F),X.x=t→X.width=o.K→∀ i∈ D,
   0≤ A i ∧ A i≤1∧ ∀ b:Air f G,|Fan.vows X R Q o.a p b i| ≤ A i*β^(levy z' i))
variable (hI:∀ (F: Forest S.ratio)(X:Coat T F),X.x=t→X.width=o.K→ (Fan.pool (Field.pin D H) X p).real (cabinet (Field.pin D H) (postponement L t o))ᶜ ≤ K₀)
variable (u:H.ThinP)(hu: u.val=Fan.arm D) (hK:Ac.Spark H.supportP u.val)(he:troupe T R Q.halo (radiusB t) u.val)
include K hp hP hT hI hA hu hK he hB
lemma tentacles (n:ℕ) :
     ‖leaflet H χ (increment 1 x) u - ∑ i:LevelsΛ D n, perLeaf χ D H i p‖ ≤ ℋ^D.card * Z *(K₀+D.card*(β^mini)^n) :=by
  letI : Nonempty (Forest S.ratio) := Tree.select S.ratio S.patch.odd_side
  let I:= Field.pin D H
  have hs:= thrones D H K u hu hK he p (increment 1 x) (by rw [hP]) hp
  rw [hs]; unfold perLeaf; rw [questv (ι:=Reserve S) (f:=fun i (z:LevelsΛ D n)=> likely (fun k=> curlP ((Greenbelt.prism T t χ o.K (1:Config G c) (Greenbelt.allot (S:=S) i)).taggedL k) R D Q.table d I p z))]
  apply difference; intro i
  let X k:= (prism T t χ o.K 1 (Greenbelt.allot (S:=S) i)).taggedL k
  rw [questv (ι:= S.Choices) (f:=fun k (q:LevelsΛ D n)=> curlP (X k) R D Q.table d (Field.pin D H) p q)]; apply difference; intro k
  let Y:= X k; have hg := hA _ Y rfl rfl; have hh : (timeΛ Y p).manifest:= by
       change ∅ = RG.flags (Pressure.temp t) (increment (1: Config G c) p.2); rw [hP]; exact hp.symm
  have ht:= packed Y D I p H rfl rfl hh (show postponement L t o = d from rfl) hT x hP (zero_lt_one.trans_le hB) A (levy z') (fun i hi=> (hg i hi).1) (fun i hi=> (hg i hi).2.1) (fun i hi=>fun b=>(hg i hi).2.2 _) n
  have hx:= shipments Y p H (
    rfl) rfl hh D I hB z' A hg n d K₀ (hI _ Y rfl rfl)
  dsimp only at hx; rw [ht] at hx; exact hx
omit K hI hu hK he
lemma bloom (y:LevelsΛ D n) : ‖perLeaf χ D H y p‖ ≤ Z*β^(tones D (levy z') y):=by
    letI : Nonempty (Forest S.ratio) := Tree.select S.ratio S.patch.odd_side
    apply avgBound; intro i; apply avgBound; intro k
    let Y:= (Greenbelt.prism T t χ o.K 1 (Greenbelt.allot (S:=S) i)).taggedL k; have hg:= hA _ Y rfl rfl
    have hh : (timeΛ Y p).manifest:= by change ∅ = RG.flags (Pressure.temp t) (increment (1: Config G c) p.2); rw [hP]; exact hp.symm
    exact (taxing Y D _ p H rfl rfl hh rfl hT x hP (zero_lt_one.trans_le hB) A (levy z') (fun i hi=> (hg _ hi).1) (fun i hi=> (hg _ hi).2.1) (fun i hi _=> hg _ hi|>.2.2 _) y).2.2
end
end YM.LocalLTE.Fan.Field
