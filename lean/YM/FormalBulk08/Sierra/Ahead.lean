import YM.FormalBulk08.Sierra.Settlers

/-! User reserves center synchronized with measurement lambda. Use l1 metric.
Equivalent at bounded displacement; fix ancestor of floored peak. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sierra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Dove Spruce Elm
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{X I:Type}{ρ:ChartRatio G}{T:I→Pot G}{τ:Time X}{W:Lab G K X}{m:ℕ}
-- λ relative arbitrary origin mesh k
abbrev Rel (S:Schedule)(k i:ℕ):ℝ≥0:=⟨S.a i / S.a k,div_nonneg (S.a_pos _).le (S.a_pos _).le⟩
lemma relPos (S : Schedule)(k i:ℕ):0 < Rel S k i:= by exact_mod_cast (div_pos (S.a_pos i) (S.a_pos k))
lemma rel_step (S:Schedule)(k i:ℕ): Rel S k i=(S.block i).val*Rel S k (i+1):= by
    ext1; push_cast;change S.a i/S.a k=(S.block i).val*(S.a (i+1)/S.a k); rw [Schedule.a_step]; field_simp
lemma anchor_rel (S:Schedule)(k i:ℕ): min 1 (Rel S k i) ≤ (S.block i).val * min 1 (Rel S k (i+1)):= by
    rw [rel_step S k i]; rcases le_total 1 (Rel S k (i+1)) with he|he
    · rw [min_eq_left he,mul_one]; exact le_trans (min_le_left ..) (Nat.one_le_cast.mpr (S.block i).pos)
    rw [min_eq_right he]; exact min_le_right ..

def pap (S:Schedule)(k:ℕ)(Z:Track)(i:ℕ):Track:= ((Rel S k i :ℝ)⁻¹) • Z
def mast (A:Levels G)(a:hue G)(x:Cover):ℕ→ℕ→edgeL G
   | 0,_=> (x,Exterior.coord 0,a)
   | n+1,i=> (Stationary.rent (A.S.block i) (mast A a x n (i+1)).1, Exterior.coord 0,a)
-- arbitrary Z measurement position. Round components
abbrev rounding (v:Track):Cover:= fun i=>Int.floor (v i)
variable (W) (a:hue G)(C:Pin W.scrolls)(k:X→ℕ)(Z:X→Track)
def signup : Trail W C a where
   root i:=mast (W.V i.a) a (rounding (pap (W.V i.a).S (k i.a) (Z i.a) (C.N i.a))) (C.N i.a-i.b) i.b
   rate i:=min 1 (Rel (W.V i.a).S (k i.a) i.b)
   cap i:=min_le_left ..
   link i:=by rw [show C.N i.bed.a-i.bed.b=C.N i.ups.a-i.ups.b+1 from ?_,mast]; rfl
              change C.N i.a-i.b=C.N i.a-(i.b+1)+1; have :=i.head;omega
   anchor i:=anchor_rel (W.V i.a).S _ i.b
variable {W C Z k a}
def Ahead (o: Trail W C a)(k:X→ℕ)(Z:X→Track):Prop := (∀ (i:Deck C),o.rate i=min 1 (Rel (W.V i.a).S (k i.a) i.b)) ∧ ∀ (i:Deck C)(b:Axis), |pap (W.V i.a).S (k i.a) (Z i.a) i.b b-(((o.root i).1 b :ℤ):ℝ)| ≤3
lemma approaching (i:Turn C)(Z:Track)(k:ℕ): (Rel (W.V i.a).S k i.ups.b)>0 ∧ pap (W.V i.a).S k Z i.ups.b=((W.liftF i).L.val:ℝ) • pap (W.V i.a).S k Z i.b:= by
    let S:= (W.V i.a).S; let L:= (W.liftF i).L; refine ⟨relPos ..,?_⟩; unfold pap; ext1 x; simp only [Pi.smul_apply,smul_eq_mul]
    rw [rel_step _ _ i.b, NNReal.coe_mul,NNReal.coe_natCast]; change _=(L.val:ℝ) * ((((L.val:ℝ)*(Rel S k i.ups.b:ℝ))⁻¹)*Z x); field_simp; rfl
lemma ahead (W:Lab G K X)(C:Pin W.scrolls)(a:hue G)(Z:X→Track)(k:X→ℕ): Ahead (signup W a C k Z) k Z:= by
   let T:= signup W a C k Z; refine ⟨fun i=>rfl,fun i b=>?_⟩
   let B(i:X)(j:ℕ):Track:=pap (W.V i).S (k i) (Z i) j
   have h(i:X)(j:ℕ)(he: W.neck i≤j)(hy:j≤C.N i):let t: Deck C:= ⟨⟨i,j,he⟩,hy⟩; |B i j b- (((T.root t).1 b:ℤ):ℝ)|≤3:= by
       induction hy using Nat.decreasingInduction with
       | self=> intro t; change |B i (C.N i) b- ((mast (W.V i) a (rounding (B i (C.N i))) (C.N i-C.N i) _).1 b:ℝ)|≤ _; rw [Nat.sub_self,mast]; let v:=B i (C.N i); change |v b- ((Int.floor (v b)):ℝ)|≤ _; have hh:= Int.floor_le (v b); have hp:=Int.lt_floor_add_one (v b);rw [abs_of_nonneg (sub_nonneg.mpr hh)];linarith
       | of_succ j hz IH=>
          intro t;let x:Turn C:=⟨⟨i,j,he⟩,hz⟩; have hh:= IH (he.trans (Nat.le_succ _)); let L: Side:= (W.V i).S.block j
          have hl: (3:ℝ) ≤ L.val:= Nat.cast_le.mpr ((W.V i).S.block_large j)
          have hp : 0 < (L.val:ℝ):= by positivity
          have ht := congr_fun ((approaching x (Z i) (k i)).2) b; let v:= T.root x.bed; let w:=T.root x.ups;change B i (j+1) b=(L.val:ℝ)*B i j b at ht
          let y:= Bank.scroll L _ w; let E:= y.2.1; have h : w.1 b= (lift E b) +((L.val:ℤ)* v.1 b):= by
             have he:v.1= y.1:=congr_arg Prod.fst (T.link x)
             rw [he]; have hh:= congr_arg Prod.fst ((Bank.scroll L (Loc G 1)).symm_apply_apply w); exact Eq.trans (congr_fun hh.symm b) (by change (lift E+ L.val • y.1) b=_;simp)
          have hw: (w.1 b:ℝ)= (lift E b:ℝ)+(L.val:ℝ)*(v.1 b:ℝ):=by exact_mod_cast h
          have hy: |(lift E b:ℝ)|≤ L.val:= by rw [←Int.cast_abs,←Int.natCast_natAbs];exact_mod_cast (show (lift E b).natAbs≤ L.val by have h:= lift_centers E b;omega)
          change |B i j b-(v.1 b:ℝ)|≤ _; rw [←mul_le_mul_iff_right₀ hp, ← abs_of_nonneg hp.le,←abs_mul]
          have He:(L.val:ℝ)* (B i j b-v.1 b)= (B i (j+1) b- (w.1 b:ℝ))+(lift E b:ℝ):= by rw [ht,hw];ring
          rw [He]; refine (abs_add_le ..).trans ((add_le_add (show |B i (j+1) b-(w.1 b:ℝ)|≤3 from hh) hy).trans ?_); rw [abs_of_nonneg hp.le]; linarith only [hl]
   exact h i.a i.b i.zone i.cap
end YM.FormalBulk08.Sierra
