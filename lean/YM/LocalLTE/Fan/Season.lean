import YM.LocalLTE.Fan.Dye
/-! Integrated b,x Taylor through D(q). Coefficient is formed by one joint polynomial on drift A and χ virtual fields. -/
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
open Brush Foramen Pastel Bakers PhysicalNext.Repeat Greenbelt Blaze.Stained Gas Ursell
variable {v z r W w s t y η γ B a μ b C C' q X Y : ℝ} {j n k m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}{χ:Chi}
variable (H:Cash W t μ L Q o a T R)
variable (K:Captain H j C v z r Y C' w B q m χ)
variable {p:ℕ} (D:Slots p→Finset (Veil c f)) (V:Tuple H.ThinP p)
section
variable (β:ℝ)(e :ℕ→ℕ)(U: Veil c f→ℝ)
def castRank (p:ℕ)(q:ℕ):ℝ:= chip (q+1)-20*slack + (1/2:ℝ)*p
def hCost (B:ℝ)(p _q m:ℕ) := B^(p+1)*(1+(p+1:ℕ))^m -- edit q
lemma strength (z:Disk G c)(p':ℕ)(hk:1≤k)(h:∀ i,(D i).card≤ N)(h₀:∀ i k,k ∈ D i→ 0≤U k)(hβ:1≤β)(he:∀ i k,Sum.inl k∈ D i → e k≤ p')(hp:∃ i k,Sum.inl k∈ D i)
    (hP:∀ i(w:LevelsΛ (D i) k)(r:Greenbelt.Reserve S)(j:S.Choices), Brush m ((Field.oiled D U i * β^(tones (D i) (Fan.jumpP e) w))*B) 1 (fun x=> Bakers.curlP ((prism T t χ o.K (1:Config G c) (Greenbelt.allot r)).taggedL j) R (D i) Q.table (postponement L t o) (Field.pin (D i) H) x w) z)
    (hB :0 ≤ B): Brush m ((Field.stock D U *β^(castRank (pie p'+1) p'))* (((k:ℝ)^N)^(p+1)* hCost B p k m)) 1 (fun x=> rune H D x k e χ p') z:=by
  let Z x (q : Gains D k):= if built D q (levy e) ≥ chip (p'+1)-10*slack then lace H D x q χ else 0
  let A:= Field.stock D U * β^(castRank (pie p'+1) p'); let J:= hCost B p k m; have hA:0 ≤ A:=mul_nonneg (prod_nonneg (fun j _=> oil_nonneg D h₀ j)) (Real.rpow_nonneg (zero_le_one.trans hβ) _)
  have hJ:0≤J:=by unfold J hCost; positivity
  have he q : Brush m (A*J) 1 (fun x=> Z x q) z:=by
    by_cases hx: built D q (levy e) ≥ chip (p'+1)-10*slack
    swap; · exact Brush.zi (Eventually.of_forall fun _=>if_neg hx) (mul_nonneg hA hJ) zero_le_one
    have hu:built D q (Fan.jumpP e) ≤ castRank (pie p'+1) p':=by
      have h:= extendH D q e hp he hx; unfold castRank; linarith only [h]
    letI : Nonempty (Tree.Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
    have hp i : Brush m _ 1 (fun z=> perLeaf χ (D i) H (q i) z) z:= Captain.avgBrush _ _ _ (fun r=> Captain.avgBrush _ _ _ (fun j=> hP i _ r j))
    apply ((Brush.all_prod _ _ _ _ (fun i _=> hp i)).trim).climb _ le_rfl|>.shimmy
    · exact Eventually.of_forall fun x=> if_pos hx
    simp only [Finset.prod_mul_distrib,Finset.prod_const,sum_const,Slots, card_univ, Fintype.card_option,Fintype.card_fin,nsmul_eq_mul,mul_one]
    have hm:Field.stock D U * β ^(built D q (Fan.jumpP e)) ≤ A:= mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hβ hu) (prod_nonneg fun _ _=> oil_nonneg D h₀ _)
    unfold built at hm; rw [Real.rpow_sum_of_pos (zero_lt_one.trans_le hβ)] at hm
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hm hJ); unfold Field.stock J hCost; ring -- edit
  refine (Brush.spree univ _ _ zero_le_one (fun i _=> he i)).climb ?_ le_rfl
  rw [sum_const,nsmul_eq_mul]; apply le_trans (mul_le_mul_of_nonneg_right (show ((univ:Finset (Gains D k)).card:ℝ) ≤ ((k:ℝ)^N)^(p+1) from by rw [Finset.card_univ]; exact launches D h k hk) (mul_nonneg hA hJ)); apply le_of_eq; unfold A J; ring -- edit
end
-- sung w/o Ursell factor as (g,atom power) at actual.
def forecast (m k:ℕ) (e:ℕ→ℕ)(χ:Chi) := LocalLTE.stem (pie m+1) (fun x=> rune H D x k e χ m)
section issue
variable (x: Disk G c)(u:Directions G c)(hu:x=(gStep R.beta,u))
variable {u₀:ℝ} (β:ℝ)(hB:1 ≤ β)(z':ℕ→ℕ)(A:Veil c f→ℝ) (hk:1≤k)
variable (hp:flags (Pressure.temp t) (increment (1: Config G c) u)=∅)(hT:Stamp T)
variable (hA:∀ (F: Forest S.ratio)(X:Coat T F),X.x=t→X.width=o.K→∀ k,∀ i∈ D k,
   0≤ A i ∧ A i≤1∧ ∀ b:Air f G,|Fan.vows X R Q o.a x b i| ≤ A i*β^(levy z' i))
variable (hI:∀ k,(D k).card≤ N∧ ∀ (F: Forest S.ratio)(X:Coat T F),X.x=t→X.width=o.K→ (Fan.pool (Field.pin (D k) H) X x).real (cabinet (Field.pin (D k) H) (postponement L t o))ᶜ ≤ u₀)
variable (he:∀ i,(V i).val=arm (D i) ∧ Ac.Spark H.supportP (V i).val ∧ troupe T R Q.halo (radiusB t) (V i).val)

def leftOver (p N k z:ℕ)(β u₀ :ℝ):= let J:=envelope β u₀ N k; let V:=1+J+(k:ℝ)^N
      (p+1:ℕ)*J*V^(p+1)+((k:ℝ)^N)^(p+1)*β^(chip (z+1)-10*slack)
include hp hT hu hA hI he K hB hk
lemma foreword (z:ℕ)(h:0≤u₀) :
  |(∏ i,leaflet H χ (increment 1 u) (V i))-rune H D x k z' χ z| ≤ Field.stock D A * leftOver p N k z β u₀ :=by
    let a (i:Gains D k):=lace H D x i χ; let Z (i:Gains D k):= built D i (levy z'); let b:=chip (z+1) - 10*slack; let f:=∑ i,a i; let g i:= if b≤Z i then a i else 0
    have hh (i:Gains D k):=glaze H (χ:=χ) D u x hu hp hT β hB z' A hA i
    let C:=Field.stock D A
    obtain ⟨F⟩:= Tree.select S.ratio S.patch.odd_side; let Y:= prism T t χ o.K 1 F; have hc:0≤C:= prod_nonneg fun i _=> oil_nonneg D (fun i j hj=> hA _ Y rfl rfl _ _ hj |>.1) i
    have hz i (_hi:i∈(univ:Finset (Gains D k))): |a i-g i| ≤ C*β^b:= by
      unfold g; split; next => simp only [sub_self,abs_zero]; positivity
      next h=> rw [sub_zero]; exact (hh _).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hB (lt_of_not_ge h).le) hc)
    have ht: |f-∑ i,g i|≤ ((k:ℝ)^N)^(p+1)* (C*β^b):= by
      unfold f; rw [← sum_sub_distrib]; apply ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum hz)).trans; rw [Finset.sum_const,nsmul_eq_mul, card_univ]; exact mul_le_mul_of_nonneg_right (launches D (fun i=> hI i|>.1) k hk) (by positivity)
    let U:= ∏ i,leaflet H χ (increment 1 u) (V i); change |U-∑ i,g i|≤_
    rw [show U-∑ i,g i=(U-f)+(f-∑ i,g i) by ring]
    have hh:= lifting H K D V u x hu hp hT β hB z' A hA hI he h k hk; dsimp only at hh; apply ((abs_add_le ..).trans (add_le_add hh ht)).trans; unfold leftOver; dsimp only; unfold C b; apply le_of_eq; ring
end issue
end YM.LocalLTE.Fan.Field
