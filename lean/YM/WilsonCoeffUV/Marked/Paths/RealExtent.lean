import YM.WilsonCoeffUV.Marked.Paths.Fees
import YM.WilsonCoeffUV.Product.Report.Center
import YM.WilsonCoeffUV.Marked.Bounds.Wig
/-!
# Recenter NFC retain mark roots + address measures costs
 Explicit tree from χ including all roots. No real gas/indicator partners. Rank 0.
 -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Rolls
open Gauge Power PowerSeries Matrix Filter Lattice Laurent Exterior Precision Wilson RG Tree Bloch Stationary
open Function Blue Bank Fountain Soil Source Source.Drops Labels Cosmos Planned.PrimaryIntegral295 Place Carrier Bank.Carp Bank.Mosaic Bank.Mosaic.Near
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n:Side}{k h r t i j l e m b:ℕ}{s v u A B:ℝ}
variable {V W I α β:Type}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]{S : Finset I}{c:I}{o:Cover}
open Real
-- reference alias for each source a priori from Ward anchored
omit [CompleteSpace V] [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma dreams (P:Era G V)(o:Cover): shifted (shifted P (-o)) o=P:=by
    apply Prod.ext
    · funext n i j x; unfold shifted skewV revolve; dsimp only; rw [show ⇑(jog (-wrap n (-o))) ∘ (⇑(jog (-wrap n o)) ∘ x)=x from ?_];
      funext i; rw [map_neg]; apply Prod.ext <;> simp [Bank.jog]
    funext i j x; unfold shifted skewV revolve; dsimp only; rw [show ⇑(jog (- -o)) ∘ (⇑(jog (-o)) ∘ x)=x from ?_]; funext i; apply Prod.ext <;> simp [Bank.jog]
omit [NormedSpace ℝ V] [CompleteSpace V] in
lemma sigmaMint (v: Cover){P: Ten V (Cloth α) r}(n:Side): Carp.plume (revolve v P) n= revolve (wrap n v) (Carp.plume P n):= by
    classical
    let B: Equiv.Perm (dock Cover α r) := (Equiv.refl (Fin r)).arrowCongr (jog v); funext x; rw [Carp.plume,← B.tsum_eq]; unfold revolve Carp.plume
    apply tsum_congr; intro y; unfold peglet; change (if slideC n (jog v ∘ y)=x then P (jog (-v) ∘ (jog v ∘ y)) else 0)=(if slideC n y=jog (-wrap n v) ∘ x then P y else 0)
    have ht : slideC n (jog v ∘ y)=jog (wrap n v) ∘ (slideC n y):= funext fun i=> fold_move n v (y i)
    have he{A W:Type}[AddGroup A](x:dock A W r)(p:A): jog (-p) ∘ (jog p ∘ x)=x:= by ext i <;> simp [jog]
    have hs: slideC n (jog v ∘ y)=x ↔ slideC n y=jog (-wrap n v) ∘ x :=⟨fun p=> by rw [← p,ht]; exact (he ..).symm,fun p=>by rw [ht,p]; simpa only [neg_neg] using (he x (-wrap n v))⟩
    split_ifs with hv hu hu; rw [he]; apply False.elim; exact hu (hs.mp hv); apply False.elim; exact hv (hs.mpr hu); rfl
-- (Vector) mark diameter passive before translation
open Wheel Wheel.Mark
def realmSize (S:Finset I)(p:I→Cover):= league Bank.terrain (fun i:S=>p i.val)
lemma nested_u (p:I→Cover)(w:dock Cover α r) : realmSize S p≤ Syn Bank.terrain p S w:= by
    refine league_le Bank.terrain _ (fun i j=>?_); exact leg_le Bank.terrain (foyer p S w) (Sum.inl i) (.inl j)
omit [NormedSpace ℝ V][CompleteSpace V] in
lemma skyRoot (X:Ten V (Cloth α) r)(z:I→Cover)(p:Wig Bank.terrain z s A S X)(h:c ∈ S)(g:0<s): Cork Bank.terrain 0 (s/2) (A*Real.exp (-s/2*realmSize S z)) (revolve (-(z c)) X):=by
    let u:= z c; have he:= (Wig.to_cork p g.le h); refine ⟨mul_nonneg p.1 (by positivity),fun x=>?_⟩
    let y:=jog (- -u) ∘ x; let d:=realmSize S z; let t:=tread Bank.terrain 0 x; have hv:t=tread Bank.terrain u y:=by
       unfold t y; convert! rev_league (-u) _ u x
       · simp
       intro a b; simp [Bank.terrain]
    have hx:(t:ℝ) ≤ Syn Bank.terrain z S y:= by
       rw [hv]; exact Nat.cast_le.mpr (league_le Bank.terrain _ fun a b=> by
         let f : Fin (r+1)→ S⊕ Fin r := Fin.cases (.inl ⟨c,h⟩) Sum.inr; have ht j:stud u y j=foyer z S y (f j):=Fin.cases rfl (fun _=>rfl) j
         rw [ht,ht]; exact leg_le ..)
    have hvd :(d:ℝ) ≤ Syn Bank.terrain z S y:= by exact_mod_cast (nested_u (S:=S) z y)
    refine (p.2 y).trans ?_; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ p.1; rw [←Real.exp_add,Real.exp_le_exp]; change _≤ -s/2*d+ -(s/2)*t; linarith only [mul_le_mul_of_nonneg_left hvd g.le,mul_le_mul_of_nonneg_left hx g.le]
lemma root_robe (R: Robes G V k)(h:Rains R i s A)(hp:0<s)(o:Cover) : let X:= shifted (baton R i) o; Auth k X ∧ ∀ n:Side,∀ j k,X.1 n j k=Carp.plume (X.2 j k) n:=by
    intro X; refine ⟨(sufficesR h hp).shifted _,fun n j k=>?_⟩; unfold X; unfold shifted skewV; simp only [sigmaMint, mooring h hp]
-- root cost accounting: exponent path ∑ slots + deterministic stubs from TEST ROOT to distinguished χ

def feeH (z:I→ Cover)(c:I)(S:Finset I):= S.card+∑ i∈S,Bank.terrain.gap (z c) (z i)
omit [NormedSpace ℝ V][CompleteSpace V] in
lemma feeH_le (z:I→Cover)(h:c ∈ S): feeH z c S≤ S.card*(1+realmSize S z):=by
    unfold feeH; apply le_trans (Nat.add_le_add_left (Finset.sum_le_sum (g:=fun _=> realmSize S z) (fun i hi=> leg_le Bank.terrain (fun i:S=>z i.val) ⟨c,h⟩ ⟨i,hi⟩)) _) (by simp [mul_add])

def tenure (R:Robes G V k)(S:Finset I)(z:I→ Cover)(c:I)(e:ℕ)(s x:ℝ): Prop:=∀ j<e,∀ r: Fin (k+j+1), SumBudget (fun i=> Real.exp (s*feeH z c S)*integerP (R j r i) s) x

def sphere (P:Era G V)(k i:ℕ) (c:I)(z:I→ Cover): Robes G V k:= automa (shifted P (-z c)).2 k i
lemma shineZ (P:Era G V)(z:I→Cover) (H:Rains (sphere P k t c z) t s A)(x:0<s)(v:∀ j< t,(baton (sphere P k t c z) t).2 j=(shifted P (-z c)).2 j)(j:ℕ)(p:j< t): let Q := shifted (baton (sphere P k t c z) t) (z c); Q.2 j=P.2 j ∧ ∀ n r,Q.1 n j r=Carp.plume (P.2 j r) n:=by
    intro Q; let W:=(sphere P k t c z); let X:= shifted P (-(z c)); have ht : Q.2 j= P.2 j:= by
       trans (shifted X (z c)).2 j; · funext r; exact congr_arg (revolve (z c)) (congr_fun (v j p) r)
       rw [show shifted X (z c)=P from dreams P (z c)]
    refine ⟨ht, fun n r=>(Eq.trans (show Q.1 n j r=Carp.plume (Q.2 j r) n from (root_robe W H x _).2 n j r) (congr_arg (Carp.plume · n) (congr_fun ht r)))⟩
lemma planet (G:Gauge)(b k e:ℕ)(s:ℝ)(g:0<s):∃ t:ℝ,∃ C:ℝ,0<t∧t≤s∧0≤ C∧∀ (V:Type)[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V] (P:Era G V)(I:Type)(S:Finset I)(z:I→Cover)(c:I) (A:ℝ), Auth k P→ c∈S → S.card≤ b → 0≤A →(∀ i<e,∀ j,Wig Bank.terrain z s A S (P.2 i j)) → ∀ j ≤ e,
  let Q := sphere P k j c z; Rains Q j t (C*A*Real.exp (-s/2*realmSize S z)) ∧ tenure Q S z c j t (C*A*Real.exp (-s/4*realmSize S z)) ∧ ∀ v < j,(baton Q j).2 v=(shifted P (-z c)).2 v:=by
    obtain ⟨w,L,x,hp,hv,H⟩:= autoK G (s/2) e k (half_pos g); let t:=min w (s/(4*(b+1:ℝ))); have he:0<t:= lt_min x (by positivity); let C:= Real.exp (s/4)*L; have hc:L≤ C:=le_mul_of_one_le_left (zero_le_one.trans hv) (Real.one_le_exp (by linarith))
    refine ⟨t,C,he,((min_le_left ..).trans hp).trans (half_lt_self g).le,zero_le_one.trans (hv.trans hc),?_⟩; intro V _ _ _ P I S z c A v u h hA X j f Q
    let p:=realmSize S z; let R:=shifted P (-z c); let E:= A*Real.exp (-s/2*p); have ht:Rain R.2 e (s/2) E:=⟨mul_nonneg hA (by positivity),fun i h j=> skyRoot _ z (X i h j) u g⟩; obtain ⟨a,y⟩:= H j f V R.2 E (nimb R (v.shifted _) e) ht
    have hy:= Rains.slack a (u:=t) (min_le_left ..) le_rfl
    refine ⟨hy.slack le_rfl (le_trans ?_ (show C*E=C*A*Real.exp _ from ?_).le),fun l u' r=>?_,y⟩
    · apply mul_le_mul_of_nonneg_right hc ht.1
    · unfold E p; ring
    let d:=feeH z c S; refine cap_raise (cap_scale (hy.2 _ u'|>.2 r).2 (show 0≤Real.exp (t*d) from by positivity)) ?_
    have hh: t ≤ s/(4*(b+1:ℝ)):=min_le_right ..
    have ha:= (le_div_iff₀ (by positivity)).mp hh
    have hf : (d:ℝ)≤ b*(1+(p:ℝ)):=by exact_mod_cast (Nat.le_trans (feeH_le z u) (Nat.mul_le_mul_right (1+p) h))
    unfold C E
    calc
     _= L*A* (Real.exp (t*d)* Real.exp (-s/2*p)):=by ring
     _ ≤ L*A*(Real.exp (s/4)*Real.exp (-s/4*p)):=by
       apply mul_le_mul_of_nonneg_left _ (mul_nonneg (zero_le_one.trans hv) hA); rw [←Real.exp_add,←Real.exp_add, Real.exp_le_exp]; nlinarith
     _ = _:=by unfold p; ring
end YM.WilsonCoeffUV.Mer.Rolls
