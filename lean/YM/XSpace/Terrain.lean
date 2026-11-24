import YangMills.WilsonProof.GraphOperands
import YM.XSpace.CorePt
import YM.XSpace.Hook
import YM.XSpace.KPos
/-!
# Point kernel alphabet for first order diagrams
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Structure1
open Filter Set Function Lattice Chart2 Mu Furlough Normalize Foundation JetGauge Outline Shade Future
open scoped Topology BigOperators Classical
variable {G:Gauge} (W:Initialize G) (d:ℕ)(a:ℝ) (x: Cover) {I:Type} {j n :ℕ}
abbrev HP (G:Gauge)(j:ℕ):= ↥(On.Grade G j)
private def mark (j:ℕ)(x:Cover): HP G j→ₗ[ℂ] PowerSeries (Stamp G):= (toy (W.surveys j) x).toLinearMap ∘ₗ (Labels.localFields G j).subtype ∘ₗ (W.surveys j).insertW (-1) ∘ₗ Furlough.Lm j
def star0 (j:ℕ)(x:Cover): HP G j→ₗ[ℂ] Stamp G:= base a^j • ((PowerSeries.coeff (R:= Stamp G) 0).restrictScalars ℂ ∘ₗ mark W j x)
def star1 (j:ℕ)(x:Cover): HP G j→ₗ[ℂ] Stamp G:= base a^j • ((PowerSeries.coeff (R:= Stamp G) 1).restrictScalars ℂ ∘ₗ mark W j x)
lemma base_mark0 (p:HP G j): star0 W a j x p=base a^j • p0 (W.surveys j) x (Prelude.startField (W.surveys j) p).val:=by rw [star0,LinearMap.smul_apply,LinearMap.comp_apply]; rw [LinearMap.restrictScalars_apply,PowerSeries.coeff_zero_eq_constantCoeff_apply]; rfl
lemma base_ice0 (p:HP G j): star0 W a j x p=freeze (snaps W p x a):= by rw [base_mark0,p0,cold,snaps,map_smul]
lemma base_mark1 (p:HP G j):star1 W a j x p= base a^j • p1 (W.surveys j) x (Prelude.startField (W.surveys j) p).val:=rfl
lemma base_ice1 (p:HP G j):star1 W a j x p= base a^j • freeze (Foundation.stars W x p):= by rw [base_mark1]; congr 1; exact hot W x p
abbrev jobs (d:ℕ):= Fin (d+1)
def assemble (M:∀ j:ℕ,HP G j→ₗ[ℂ] Stamp G): Sec G d→ₗ[ℂ] Stamp G:=∑ i:jobs d, M i ∘ₗ Normalize.part d i
abbrev μ0 := assemble (G:=G) d (fun i=> star0 W a i x)
abbrev μ1 := assemble (G:=G) d (fun i=> star1 W a i x)
lemma entry (M:∀ j:ℕ,HP G j→ₗ[ℂ] Stamp G)(p:HP G j)(h:j≤d): assemble d M (en h p) = M j p:=by
  unfold assemble; rw [LinearMap.sum_apply]; let k:jobs d:=⟨j,Nat.lt_add_one_iff.mpr h⟩; rw [Finset.sum_eq_single k]; change M j (Normalize.part d j (en h p))=_; rw [part_same]; intro z _ hz; rw [LinearMap.comp_apply,part_other p (fun H=>hz (Fin.ext H)),map_zero]; simp
variable (x: Fin n→Cover)
abbrev Tags (G:Gauge)(d n:ℕ):= Fin n→Sec G d
def wind (b:Fin n→ Sec G d→ₗ[ℂ] Stamp G) := (MultilinearMap.mkPiAlgebra ℂ (Fin n) (Stamp G)).compLinearMap b
include d in
lemma winds (b:Fin n→ Sec G d→ₗ[ℂ] Stamp G)(p: Tags G d n): wind d b p=∏ i,b i (p i):=rfl
def snow (q:Face ℤ): Point G d n:= ((E (Mu.root G)) ∘ₗ LinearMap.mulLeft ℂ (V3 G q)).compMultilinearMap (wind d (fun i=> μ0 W d a (x i)))
def blossom0 : Point G d n:= (E (Mu.root G)).compMultilinearMap (wind d (fun i=> μ0 W d a (x i)))
def blossom1 : Point G d n:= ∑ i:Fin n,(E (Mu.root G)).compMultilinearMap (wind d (update (fun i=> μ0 W d a (x i)) i (μ1 W d a (x i))))
variable {d} {D:Fin n→ ℕ}
abbrev shells (D:Fin n → ℕ)(p:∀ i:Fin n,HP G (D i))(h:∀ i,D i≤d):=fun i=> en (h i) (p i)
variable (p:∀ i:Fin n,HP G (D i))(h:∀ i,D i≤d)
lemma blossoms : blossom0 W d a x (shells D p h)= baseZero W Finset.univ p a x:=by unfold blossom0 baseZero; rw [LinearMap.compMultilinearMap_apply,winds]; unfold μ0 shells; simp_rw [entry,base_ice0]; rfl
lemma snowflake (q:Face ℤ): snow W d a x q (shells D p h)= Foundation.sends q (sess W Finset.univ p a x):=by unfold snow Foundation.sends; rw [LinearMap.compMultilinearMap_apply,winds]; unfold μ0 shells; simp_rw [entry,base_ice0]; rfl
lemma pointed (b:Fin n→ Sec G d→ₗ[ℂ] Stamp G)(v: Sec G d→ₗ[ℂ] Stamp G) (i:Fin n)(p: Tags G d n): wind d (update b i v) p=v (p i)*∏ j∈Finset.univ.erase i, b j (p j):= by
  rw [winds,← Finset.mul_prod_erase _ _ (Finset.mem_univ i), update_self]; congr 1; exact Finset.prod_congr rfl fun j hj=> by rw [update_of_ne (Finset.mem_erase.mp hj).1]
lemma pointer (i:Fin n)(p:Tags G d n)(v:Sec G d): blossom0 W d a x (update p i v)=E (Mu.root G) (μ0 W d a (x i) v*∏ j∈Finset.univ.erase i, μ0 W d a (x j) (p j)):=by
  unfold blossom0; rw [LinearMap.compMultilinearMap_apply,winds,← Finset.mul_prod_erase _ _ (Finset.mem_univ i),update_self]; apply congr_arg; apply congr_arg; exact Finset.prod_congr rfl fun j hj=> by rw [update_of_ne (Finset.mem_erase.mp hj).1]
lemma prime_bloom : blossom1 W d a x (shells D p h)= hotspot W Finset.univ p a x:=by unfold blossom1 hotspot; rw [sum_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [LinearMap.compMultilinearMap_apply,pointed]; unfold shells μ0 μ1; simp_rw [entry,base_ice0,base_ice1,smul_mul_assoc,map_smul]; rfl
lemma sums (q:PlaqAxes)(p:Tags G d n) : Summable fun i:Cover=> snow W d a x (i,q) p:=by
  simp_rw [calls (snow W d a x (_,q)) p]; apply summable_sum; intro b _; let v (j:Fin n): HP G (b j).val:=Normalize.part d (b j) (p j)
  change Summable fun i=> snow W d a x (i,q) (shells (fun j=> (b j).val) v (fun j=> Nat.lt_add_one_iff.mp (b j).isLt)); simp_rw [snowflake]; exact sweeping ..
def integralPart (d:ℕ)(q:PlaqAxes): Point G d n:= MultilinearMap.mk' (fun p=>∑' i:Cover, snow W d a x (i,q) p) (by intro p i f g; simp_rw [MultilinearMap.map_update_add]; exact (sums W a x q _).tsum_add (sums W a x q _)) (by intro p i c v; simp_rw [MultilinearMap.map_update_smul,smul_eq_mul,tsum_mul_left])
def replied (d:ℕ):Point G d n:= blossom1 W d a x- ∑ q:PlaqAxes, integralPart W a x d q
lemma raw1 : replied W a x d (shells D p h)= Foundation.basic W Finset.univ p a x:=by
  rw [Foundation.exposure,replied,sub_apply,sum_apply,prime_bloom]; apply congr_arg; refine Finset.sum_congr rfl fun j _=>tsum_congr fun i=> snowflake ..
end YM.XSpace.Structure1
