import YM.OPE.Compatible.Slope.Coat
/-!
# Product-soft powers
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG Finset Next.Free Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {r k j n:ℕ}{v:ℝ}{P:Flight j k}{L:Side}
lemma arrayRead (f:Fin r→ Cover→ℝ) (h:∀ i,Summable (f i)): HasSum (weave f) (∏ i,(∑' j,f i j)):=by
   induction r with
   | zero=>
      haveI: Fintype (Bin 0):= Fintype.ofFinite _; letI:Unique (Bin 0):=inferInstance
      convert hasSum_fintype (weave f) using 1; simp [weave]
   | succ n ih=>
      let g(j: Fin n):= f j.succ; let V:= weave g; let K:= couple n; let z:Cover×Bin n→ℝ:= fun i=> f 0 i.1*V i.2
      have hs:= ih g (fun j=> h _); have hW : Summable z:= ((h 0).norm.mul_norm hs.summable.norm).of_norm -- lemma
      have he : weave f=z ∘ K:=by ext1 x; change (∏ i, _) = _; rw [Fin.prod_univ_succ];rfl
      have hz : Summable (z ∘ K) := K.summable_iff.mpr hW
      rw [he, Fin.prod_univ_succ,← hs.tsum_eq]; convert! hz.hasSum using 1; simp_rw [comp_apply]; rw [K.tsum_eq]; exact (h 0).tsum_mul_tsum hs.summable hW
lemma overall {X:Lines L}(h: Next.Free.Whole X)(a b:Axis)(x:Cover)(m:ℕ):∃ C:ℝ,Sack (poise m) (fling X a b x) C:=by
    obtain ⟨η,C,hp,hH⟩:=h; let y:=cellar L x
    have he:= fling_budget hH hp a b m x
    have ht: 0 ≤ poise m y:= zero_le_one.trans (poise_one m y)
    refine ⟨poise m y*(widthCost η m*C),?_⟩; let d(i:Cover):= poise m (i-y)*‖fling X a b x i‖; have hs:SumBudget (fun i=> poise m y*d i) (poise m y*(widthCost η m*C)):= ⟨fun i=>mul_nonneg ht (he.1 _), he.2.1.mul_left _, by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left he.2.2 ht⟩
    refine Work.F08.budget_minor hs (fun i=>mul_nonneg (zero_le_one.trans (poise_one m _)) (norm_nonneg _)) fun i=>?_ ; unfold d; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); conv_lhs=>rw [show i=y+(i-y) by abel]
    exact poise_cumul y _ m
local notation "L!"=> (linesOf P v)
local notation "Y!"=> (fun _ : Fin r=>L!)
local notation "U!"=>((P.L.val:ℝ)⁻¹)
variable (hk:4 ≤ k) (hp:0<v)
include hk hp
omit hk hp in
lemma sully {X:Lines L}(H:Next.Free.Whole X) (l:List Axis)(a b:Axis) (x:Cover)(p:Lieu Axis) :Summable fun y=> fling X a b x y * tasting l (p + translit y):=by
    let f :Lieu Axis→ Lieu Axis:= fun u=>p+u; have he (i:Axis): (fun x:Lieu Axis=> f x i)∈Flavor Axis 1:= by change ((fun _=>p i) + (fun x:Lieu Axis=>x i)) ∈ _; exact (Flavor Axis 1).add_mem (flavor_cast _ _) (flavor_position i)
    obtain ⟨B,hB⟩:= overall (X:=X) H a b x l.length; have hh:= flavor_diagonal f he (flavor_part l l.length le_rfl); change Summable (fun s=> fling X a b x s*((tasting l) ∘ f) (translit s)); exact gardens hh hB
lemma transmute {l:List (Keys r)}(h:l.length<j)(x:Bin r) (a b: Fin r→Axis) (c:Fin r→ Cover) :
   well (parcelK Y! a b c x) (tasting l)= ∑' y:Bin r,parcelK Y! a b 0 0 y * tasting l (U! • translit (x+lace r c)+translit y) := by
     let d i:= c i+stepOut x i; let t(i: Fin r):= U! • translit (d i)
     let p i(z:Cover):= fling L! (a i) (b i) (d i) z * tasting (tasteE l i) (translit z); let q i(z:Cover):= fling L! (a i) (b i) 0 z * tasting (tasteE l i) (t i +translit z)
     have hu(i: Fin r): (tasteE l i).length<j:= ((single_le_sum (fun _ _=>Nat.zero_le _) (mem_univ i)).trans_eq (tram l)).trans_lt h
     have he : (∑' z:Bin r,weave p z)=(∑' z:Bin r,weave q z):=by
        have hs i:Summable (p i):=by simpa only [p,zero_add] using (sully (X:=L!) (stored P _ hp hk) (tasteE l i) (a i) (b i) (d i) 0)
        have hH i: Summable (q i):= sully (X:=L!) (stored P _ hp hk) _ _ _ 0 (t i)
        rw [(arrayRead _ hs).tsum_eq,(arrayRead _ hH).tsum_eq]; exact prod_congr rfl fun i _=> guise (P:=P) hk hp _ (hu i) _ _ _
     have hh(i:Fin r)(y): t i+translit (stepOut y i)=curry (U! • translit (x+lace r c)+translit y) i:=by ext1 z; change U!*(↑((c i) z + stepOut x i z))+_ = U!*(↑(stepOut x i z+(c i) z))+_; rw [add_comm ((c i) z)]; rfl
     have hn (i:Fin r) : (0:Fin r→Cover) i+stepOut 0 i=0 := by rw [show stepOut 0 i= (0:Cover) from rfl]; rfl
     unfold well; calc
        _ = _:= Eq.trans ?_ he
        _ = _:= tsum_congr fun i=>by
                rw [parcelK,topping,← prod_mul_distrib]
                refine prod_congr rfl fun j _=> ?_; unfold q; rw [hh,hn]
     apply tsum_congr; intro i; rw [topping]; unfold parcelK; rw [← prod_mul_distrib]; rfl
end YM.OPE.Flume
