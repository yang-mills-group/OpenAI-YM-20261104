import YM.WilsonCoeffUV.Product.I.Verse
/-!
# Evaluated step rank-hierarchy

-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Exterior Next.Free Tree Precision Power Embroider Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U α β V W E W' ι : Type*}{r h D k j l m e i:ℕ} {A:ℝ}{G:Gauge}

variable {d u σ N:ℕ}{w t:ℝ}{I:Gear G}
lemma Auth.coverN [NormedAddCommGroup V][NormedSpace ℝ V]{P:Era G V}(h:Auth k P): shellK k P.2 := fun i j p=> Bends.exten (h.wing ..) (Bends.zero.congr (Eventually.of_forall fun n=>((h.span n) i j p).symm))
lemma Auth.coverP [NormedAddCommGroup V][NormedSpace ℝ V]{P:Era G V}(h:Auth k P)(i): Pure (P.2 i):=fun j=>(h.wing i j).pure (Eventually.of_forall fun n=>h.pale n i j)
lemma Auth.safe {P:Era G ℝ}(h:Auth k P)(n:Side): rollTest (flash (P.1 n)) (flash (P.1 n)) 1 0 := by

   intro Z I z X X' E;
   exact h.token n LinearMap.id E
lemma Auth.roots {P:Era G ℝ}(h:Auth k P): vertical P.2 := by
    intro b x k; let D':= ∑ v:Axis, ∑ j:G.ColorIndex,∑ z∈Finset.antidiagonal k,(wickLamp b 0 (x,v) j z.1 (P.2 z.2)+ wickLamp 0 b (x-step v,v) j z.1 (P.2 z.2)); let K(n:Side):Gen ℝ (Co n (Hooks G)) := ∑ v:Axis,∑ j:G.ColorIndex,∑ z∈Finset.antidiagonal k, (lamp b 0 (wrap n x,v) j z.1 (P.1 n z.2)+lamp 0 b (wrap n (x-step v),v) j z.1 (P.1 n z.2)); funext l w
    have he: Tendsto (fun n=>K n l (foldUnder n ∘ w)) atTop (𝓝 (D' l w)):=by
       unfold D' K; simp_rw [Finset.sum_apply,Pi.add_apply]; apply tendsto_finsetSum; intro i _; apply tendsto_finsetSum; intro j _; apply tendsto_finsetSum; intro v hv; exact (lamp_spring b 0 (x,i) j _ (P:=fun n=> P.1 n v.2) (h.wing v.2) _ w).add (lamp_spring 0 b (x-step i,i) j _ (P:=fun n=>P.1 n v.2) (h.wing v.2) _ w)
    apply tendsto_nhds_unique he; refine tendsto_const_nhds.congr' ((eventually_ge_atTop (⟨2,by decide⟩:Side)).mono fun n hn=>?_); have hg: K n=0:=by unfold K; simp_rw [map_sub,wrap_step]; exact one_site (h.safe n) _ (h.span n) (h.pale n) hn ..
    change 0=K n l _; rw [hg]; rfl
-- cost post tests in ℓ1
section
structure DriftR (I:Gear G)(e r u:ℕ) where
   seed: Rally (e+1) 0 I
   X : Bookend ℝ G
   Y : Bookend ℝ G
   η : ℝ
   lo : 0≤η
   hi : η≤1
   jump : ℝ
   positive :0≤jump
   h : ∀ i j,lowerGrade i j e r→ YieldP 0 (η/I.patch.L.val) u jump seed.σ (X i j) (Y i j)
variable (I)
abbrev Pcross (R:Stand I)(P: Bookend ℝ G):= puck I.patch I.kernel I.angle R.R R.Q R.page P
def spurF (T:Stand I)(k m r:ℕ)(P: Bookend ℝ G): ChamberTen G ℝ r:= ∑ i∈Finset.range (k+3*m), scoop (Pcross I T P (i+1) m r)
abbrev bendCo (T:Stand I)(k:ℕ)(P:Bookend ℝ G):= windsT I.patch I.kernel I.angle T.R T.Q T.page k P
def spinCo (T:Stand I)(k e r:ℕ)(P:Bookend ℝ G):= spurF I T k e r P + ∑ j∈Finset.range e, coeff (e-j) (T.moving^j*(T.moving⁻¹)^r) • bendCo I T k P j r
def sunI (T:Stand I)(k:ℕ)(P:Bookend ℝ G):= Blue.mix T.moving (bendCo I T k P)
lemma touchedJ (T:Stand I)(P: Bookend ℝ G)(e r): scoop (Pcross I T P 0 e r)=pump (P e r) (owns _ T.Q):=by
    unfold Pcross puck; rw [level]; unfold slidesJ; rw [inspectFace]; ext1 x; rw [scoop,Bank.prism,climb_cut,climb_cut]; rfl
lemma gradation (T:Stand I)(k:ℕ)(P: Bookend ℝ G)(e r): bendCo I T k P e r= scoop (Pcross I T P 0 e r)+spurF I T k e r P:=by
    unfold bendCo windsT sluice spurF; simp_rw [show 1+k+3*e=(k+3*e)+1 by omega,Finset.sum_range_succ']; funext x; simp only [scoop,Finset.sum_apply,Pi.add_apply]; exact add_comm ..
lemma sunshineW (T:Stand I)(k:ℕ)(P: Bookend ℝ G)(e r): sunI I T k P e r=pump (P e r) (owns _ T.Q)+ spinCo I T k e r P:=by
    unfold sunI Blue.mix; rw [Finset.sum_range_succ,Nat.sub_self,coeff_zero_eq_constantCoeff_apply]; simp only [map_mul,map_pow,Stand.moving,constantCoeff_inv,back_cc T.sunshine,inv_one,one_pow,mul_one,one_smul]; rw [gradation, touchedJ]; unfold spinCo Stand.moving; abel
end
abbrev SeedR (G:Gauge)(e r u):= (fun (I:Gear G) (Y:DriftR I e r u)=> Y.seed)
abbrev Bout (G:Gauge)(e r u:ℕ)(j:ℕ){U:(i:Gear G)→Type*}(P Q:(i:Gear G)→ DriftR i e r u→ Ten ℝ (Cloth (U i)) j):= Fallow (fun _ _=>0) u (xpos e (SeedR G e r u)) (dpos e (SeedR G e r u)) (fun _ v=>v.η) (fun _ v=>v.jump) P Q
lemma meterB (G:Gauge)(e r u:ℕ): Meter (xpos e (SeedR G e r u)) (dpos e (SeedR G e r u)) (fun _ v=>v.η) (fun _ v=>v.jump) :=⟨fun _=>⟨fun v=>v.seed.rich,fun v=>v.seed.θ⟩,fun _ v=>v.lo,fun _ v=>v.positive⟩
lemma cross_due (p:i<e∨i=e∧r<m+2*j): Bout G e r u m (fun I v=>Pcross I v.seed.P v.X j i m) (fun I v=>Pcross I v.seed.Q v.Y j i m):=by
   apply slipping (G:=G) (k:=r) (o:=fun _ _=>0) (w:=fun _ _=>0) _ _ (meterB G e r u) (fun _ v=>v.hi) (F:=fun _ v=>v.X) (P:=fun _ v=>v.Y) _ p
   intro i j h; exact ⟨0,fun I=>⟨1,zero_le_one,fun v=> by simp only [pow_zero,mul_one,one_mul,smul_zero,coat0,zero_add]; exact v.h i j h⟩⟩
lemma spur_due (k:ℕ)(p:i<e∨i=e∧r≤m): Bout G e r u m (fun I v=>spurF I v.seed.P k i m v.X) (fun I v=>spurF I v.seed.Q k i m v.Y):= Fallow.sum (fun a _=> Fallow.gleanS (cross_due (G:=G) (i:=i) (m:=m) (j:=a+1) (e:=e) (r:=r) (u:=u) (by omega))) (meterB ..)
lemma bend_due (k:ℕ)(p:lowerGrade i m e r): Bout G e r u m (fun I v=>bendCo I v.seed.P k v.X i m) (fun I v=>bendCo I v.seed.Q k v.Y i m):=by
   simp_rw [gradation]; unfold lowerGrade at p; exact Fallow.plus (Fallow.gleanS (cross_due (G:=G) (i:=i) (m:=m) (j:=0) (e:=e) (r:=r) (u:=u) (by omega))) (spur_due k (by omega)) (meterB ..)
lemma silver (p:i≤ e)(a b:ℕ) : Bank.Slate (xpos e (SeedR G e k u)) (dpos e (SeedR G e k u)) (fun _ v=> coeff i (v.seed.P.moving^a*(v.seed.P.moving⁻¹)^b)) (fun _ v=>coeff i (v.seed.Q.moving^a*(v.seed.Q.moving⁻¹)^b)):=by
   obtain ⟨d,H⟩:=titles (G:=G) (i:=i) (e:=e+1) (by omega) 0 a b; refine ⟨d,fun I=>?_⟩; obtain ⟨A,h,f⟩:= H I; exact ⟨A,h,fun w=> f w.seed⟩
lemma spursDue (G:Gauge)(k e r u:ℕ): Bout G e r u r (fun I v=>spinCo I v.seed.P k e r v.X) (fun I v=>spinCo I v.seed.Q k e r v.Y):=by
   unfold spinCo; apply Fallow.plus (spur_due k (Or.inr ⟨rfl,le_rfl⟩)) _ (meterB G e r u); apply Fallow.sum _ (meterB G e r u); intro j hj; exact Fallow.st (silver (Nat.sub_le e j) j r) (bend_due k (Or.inl (Finset.mem_range.mp hj))) (meterB G e r u)
lemma pump0 (P: Ten V (YForest G) 0)[NormedAddCommGroup V][NormedSpace ℝ V]{L:Side}(Q:ropes Cover (Co L (Hooks G)) (Hooks G)): pump P (owns L Q)=P:=by
   funext x; unfold pump; rw [tsum_fintype,Fintype.sum_unique,spinJob]; simp [Subsingleton.elim default x]
-- pre for positive rank; scalar repeated no extra.
def pinCost (u:ℕ)(I:Gear G) (r:ℕ):ℝ:=if r=0 then 1 else (I.preB/I.patch.L.val*tender (Hooks G) I.s u)^r*9^u
lemma autumn_empty (G:Gauge)(p t:ℝ)(u:ℕ)(x:Fin 0→YForest G) : hedge 0 p u x=hedge 0 t u x:=by unfold hedge autumn; simp [tread,league]
lemma lowerCost (G:Gauge)(k e r u:ℕ): ∃ d:ℕ,∀ I:Gear G,∃ C:ℝ,0≤C∧ ∀ (Y:DriftR I e r u), vertical Y.X→ (∀ i,Pure (Y.X i)) →∀ A, Fruit 0 (Y.η/I.patch.L.val) u (Y.X e r) A →
   Fruit 0 Y.η u (sunI I Y.seed.P k Y.X e r) (pinCost u I r *A+C*Y.seed.x^d*Y.jump):=by
    obtain ⟨d,H⟩:= spursDue G k e r u; refine ⟨d,fun I=>?_⟩; obtain ⟨A,a,g⟩:= H I; let K:= I.patch.L; let B:=I.preB/K.val; let L:=B*tender (Hooks G) I.s u; let R:= B+I.D; let V:=veilR G u I.s R r; let Z:= zenithW G e u (r-1)
    have hs:= I.price.trans I.holds; have he:= I.pre_nn; have hh:0≤B:=by unfold B; positivity
    have hr:0≤ R:=hh.trans (le_add_of_nonneg_right (zero_le_one.trans I.bill_nn)); have hu:0≤V:= veilR_nn _ _ hs hr r; have hz:0≤Z:= costW_nn ..
    refine ⟨A+V*Z,by positivity,fun y ht hf X hp=>?_⟩; let T:= y.seed.P; let f:= y.X e r; let s:= y.η; have hA:=y.lo; have hq:=y.positive; have hv: Fruit 0 y.η u (spinCo I y.seed.P k e r y.X) (A*y.seed.x^d*y.jump):= (g y).wax; rw [sunshineW]
    have hQ: Fruit 0 s u (pump f (owns K T.M)) (pinCost u I r*X):= by
       have hY:= roses (P:=f) (o:=0) (w:=0) (η:=s) (fun _:Fin r=> T.M) hs (fun _=> B) (fun i=> T.crank.polish) (by rw [smul_zero,coat0,zero_add]; exact hp) hA y.hi
       by_cases h:r=0
       · subst r; rw [pump0,pinCost,if_pos rfl,one_mul]; unfold Fruit Award; simp_rw [autumn_empty G s (y.η/I.patch.L.val) u]; exact hp
       rw [pinCost,if_neg h,mul_assoc]; rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hY; exact hY
    have hg:0≤s/K.val:=by unfold s; positivity
    have hd: VectorWind 0 (s/K.val) u (Z*y.jump) f:= VectorWind.summer ht hf (fun i h j _=> (y.h i j (Or.inl h)).wax) hg (le_trans (div_le_self hA (by exact_mod_cast K.pos)) y.hi) y.positive
    have hy: I.D≤ R:= le_add_of_nonneg_left hh
    have hx: Fruit 0 s u (pump f (owns K T.Q)) (pinCost u I r* X+V*(Z*y.jump)) :=by
        rw [show pump f (owns K T.Q)= pump f (owns K T.M)+(pump f (owns K T.Q)-pump f (owns K T.M)) by abel]; exact hQ.plus (itR (K:=T.M) (w:=0) (by rw [smul_zero,coat0,zero_add]; exact hp) (T.crank.polish.le (le_add_of_nonneg_right (zero_le_one.trans I.bill_nn))) (y.seed.Υ.oneP.le hy) (hf e r) T.rule (by rw [smul_zero,coat0,zero_add]; exact hd) (T.rolls.le hy) hs y.lo y.hi) hA
    apply (hx.plus hv hA).more; rw [add_assoc]; apply add_le_add_right; rw [add_mul,add_mul,add_comm (V*_),←mul_assoc]; exact add_le_add_right (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) (one_le_pow₀ y.seed.rich)) hq) _
lemma roughCost (G:Gauge)(k e r u:ℕ): ∃ d:ℕ,∀ I:Gear G,∃ C:ℝ,0≤C∧ ∀ (p:Rally (e+1) 0 I)(X Y:Bookend ℝ G)(t A:ℝ),0≤t→t≤1→0≤A→ (∀ i j,i≤e→ YieldP 0 (t/I.patch.L.val) u A p.σ (X i j) (Y i j)) → YieldP 0 t u (C*p.x^d*A) p.σ (sunI I p.P k X e r) (sunI I p.Q k Y e r):=by
    obtain ⟨d,H⟩:=spursDue G k e r u; refine ⟨d,fun I=>?_⟩; obtain ⟨C,h,hg⟩:=H I; let L:= I.patch.L; let Q:= ((r+1:ℕ):ℝ)*(I.D*tender (Hooks G) I.s u)^r*9^u; have ht:=zero_le_one.trans I.bill_nn; have ha:= tender_nn (I.price.trans I.holds) (Hooks G) u; have hQ:0≤Q:=by unfold Q; positivity
    refine ⟨Q+C,by positivity,fun p X Y t A ht hp he w=>?_⟩; let S: DriftR I e r u:=⟨p,X,Y,t,ht,hp,A,he,fun i j v=> w _ _ (by unfold lowerGrade at v; omega)⟩; have hv: YieldP 0 t u (C*p.x^d*A) p.σ (spinCo I p.P k e r X) (spinCo I p.Q k e r Y) := hg S; rw [sunshineW,sunshineW]; apply ((show YieldP 0 t u (Q*A) p.σ _ _ from ?_).plus hv ht).step _ p.θ
    swap; · rw [add_mul,add_mul]; exact add_le_add_left (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hQ (one_le_pow₀ p.rich)) he) _
    rw [inspectFace,inspectFace]; unfold Q; rw [mul_assoc,mul_assoc]; apply prism_purchase (I.price.trans I.holds) p.Υ (YieldP.travel (w:=0) ht hp ?_) ht hp
    rw [smul_zero,coat0,zero_add]; exact w e r le_rfl
end YM.WilsonCoeffUV.Mer
