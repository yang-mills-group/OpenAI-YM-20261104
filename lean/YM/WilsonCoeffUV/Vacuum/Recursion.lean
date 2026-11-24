import YM.WilsonCoeffUV.Ward.Transverse
/-!
# Independent worker-eight vacuum coefficients at finite UV cutoff

Even coupling formal reset from full quadratic signal. Domain of `story m i`:
starts at `N` Wilson, validates `i≤N` (i = requested level), arbitrarily
fixed perturbative orders. Scalar emission per step only. Not actual. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{N m i:ℕ}

-- read unrotated positive jets.
def Kstar (P:Canvas G) : PowerSeries ℝ := PowerSeries.mk fun i=> readSun (P i 2)
lemma stellar_read (P:Canvas G)(i): coeff i (Kstar P)=readSun (P i 2) := coeff_mk ..
lemma cap_bide (P: Canvas G): Kstar (lop P)= Kstar P:=by unfold Kstar; congr
lemma pane_even {P:Canvas G}(h:PairP (lop P)): evenC (Kstar P):= by intro i hi; rw [stellar_read,show P i 2=0 from h i 2 (by omega),sun_zero]
lemma fuel_sum {ι:Type*}(s:Finset ι){P:ι→Ten ℝ (YForest G) 2}{A:ι→ℝ}{σ:ℝ}(h:0<σ)(he:∀ i∈s,Amber terrain σ (A i) (P i)): readSun (∑ i∈s,P i)=∑ i∈s,readSun (P i):=by
  classical
  induction s using Finset.induction_on with
  | empty=> rw [Finset.sum_empty,Finset.sum_empty,sun_zero]
  | @insert i s p ih=>
    have ht j (hj:j∈s):= he j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert p,Finset.sum_insert p,sun_add (he i (Finset.mem_insert_self ..)) (Amber.sum _ ht) h h, ih ht]
lemma bundle_cap {ι:Type*}{P:ι→ Ten ℝ (YForest G) 2} (h:∀ i,∃ σ A:ℝ,0<σ ∧ Amber terrain σ A (P i))(s:Finset ι): ∃ σ A:ℝ, 0<σ ∧∀ i∈s, Amber terrain σ A (P i):=by
    classical
    induction s using Finset.induction_on with
    | empty=> exact ⟨1,0,one_pos,by simp⟩
    | @insert i s p ih=>
      obtain ⟨a,b,hg,K⟩:=ih; obtain ⟨x,y,hx,H⟩:=h i
      refine ⟨min a x,max b y,lt_min hg hx,?_⟩
      intro j hj; rcases Finset.mem_insert.mp hj with H'|H'; subst j; exact (H.mono (min_le_right ..)).le (le_max_right ..)
      exact ((K j H').mono (min_le_left ..)).le (le_max_left ..)
lemma reval {B: PowerSeries ℝ}{P : Canvas G}(_h:constantCoeff B=1)(he:∀ i,∃ σ A:ℝ,0<σ ∧ Amber terrain σ A (P i 2)):
    Kstar (Blue.mix B P)= subst (B*X) (Kstar P)*(B⁻¹)^2:=by
    let R:= Kstar P; let F: PowerSeries ℝ→+* PowerSeries ℝ:= (substAlgHom (R:=ℝ) (HasSubst.of_constantCoeff_zero' (by simp:constantCoeff (B*X)=0))).toRingHom
    have hx: F X=B*X:= substAlgHom_X _; have hz a: F (C a)=C a:= by change substAlgHom _ _= _; rw [coe_substAlgHom]; exact subst_C a
    have ht: F R=subst (B*(PowerSeries.X: PowerSeries ℝ)) R:= by change substAlgHom _ _= _; rw [coe_substAlgHom]
    rw [← ht]; ext n; have he' := (filtered (show constantCoeff (F X)=0 by rw [hx]; simp) (shave R (n+1))).mul (Equal.refl (B⁻¹^2) (n+1))
    rw [he' n n.lt_succ_self, map_sum, Finset.sum_mul, map_sum]; simp_rw [map_mul,map_pow,hx,mul_pow,hz];
    obtain ⟨s,a,hs,H⟩:= bundle_cap he (Finset.range (n+1))
    rw [stellar_read,Blue.mix, fuel_sum _ hs ?c]
    case c=> exact fun i hi=> (H i hi).smul _
    apply Finset.sum_congr rfl; intro i hi; rw [show (C _*(B^i*X^i))*_=(C (coeff i R)*(B^i*(B⁻¹)^2))*X^i by ring, coeff_mul_X_pow',if_pos (by have := Finset.mem_range.mp hi; omega), coeff_C_mul,sun_μ, show coeff i R=readSun _ from coeff_mk .., mul_comm]
lemma begin_again {P:Canvas G}(h:constantCoeff (Kstar P)=1)(he:∀ i,∃ σ A:ℝ,0<σ ∧ Amber terrain σ A (P i 2)):
    Kstar (Blue.mix (back (Kstar P)) (lop P))=1 := by
    rw [reval (back_cc h) (show ∀ i, ∃ σ A:ℝ,0<σ ∧ Amber terrain σ A (lop P i 2) from he), cap_bide, fresh_back]; exact bridge_price h

-- adjacent updates
variable (A: Levels G) (Ñ: ChartRatio G)
abbrev Mantle (G:Gauge):= Crude G × Canvas G
abbrev topW (Ñ:Gauge)(n:Side):= lop (sprig (eWilson (G:=Ñ) (c:=n)) 2)

def tale (G:Gauge) : Mantle G:= (topW G,lop (moon G))

def unripe (N m:ℕ)(W:Crude G): Crude G:= fun n=>
    let P:= loose A m; let S:= mStep A n m; winter S (repeatF S) (freeForms A N (m+1)) (freeForms A N m) (roam A N m n) Ñ (W (n*P.L))

def season (N m:ℕ)(W:Canvas G): Canvas G:= tinge (loose A m) A.clock.kernel Ñ (plain G (freeForms A N m)) (shuttleM (conditional A N m)) (shuttleM (feedA A N m)) W

def twinkle (N m:ℕ)(T:Mantle G): Mantle G:=
    let R:= season A Ñ N m T.2
    let B:= back (Kstar R)
    (fun n=> Blue.mix B (lop (unripe A Ñ N m T.1 n)),Blue.mix B (lop R))
-- W generation from top N. totalize for asking above-N.
noncomputable def story (N m:ℕ): Mantle G:= if _h:m<N then twinkle A Ñ N m (story N (m+1)) else tale G
termination_by N-m
lemma story_top (N:ℕ): story A Ñ N N=tale G:=by rw [story,dif_neg (lt_irrefl N)]
lemma story_stride (h:m<N): story A Ñ N m= twinkle A Ñ N m (story A Ñ N (m+1)):=by rw [story,dif_pos h]

def actionW (N m:ℕ): Canvas G:= (story A Ñ N m).2
-- bigger raw including scalar. call stride m < N
def freshet (N m:ℕ): Canvas G:= season A Ñ N m (actionW A Ñ N (m+1))
def pitch (N m:ℕ): PowerSeries ℝ:= Kstar (freshet A Ñ N m)
-- field uses reset ratio (inverse here). other direction via pace.
def ratioHigh (N m:ℕ): PowerSeries ℝ:= back (pitch A Ñ N m)
lemma conduct (h:m<N): actionW A Ñ N m=Blue.mix (ratioHigh A Ñ N m) (lop (freshet A Ñ N m)):= by rw [actionW,story_stride A Ñ h]; rfl

-- closure both currencies for exact Wick/Ward/vac read
structure Hier (H:FaceRow)(U:Mantle G) : Prop where
  basis (n:Side): Interlace H (U.1 n)
  patch (i r): Yields (fun n=> U.1 n i r) (U.2 i r)
  readP : Kstar U.2=1

lemma scissors {G:Gauge}{i r:ℕ}{P:Crude G}{Q:Canvas G}(h:Yields (fun n=> P n i r) (Q i r)) : Yields (fun n=> lop (P n) i r) (lop Q i r):= by
   by_cases he:r=0; · simp only [lop,he,↓reduceIte]; exact Yields.zero
   simp only [lop,he,↓reduceIte]; exact h
lemma covers_mix {G:Gauge}{P:Crude G}{Q:Canvas G}(h:∀ i r,Yields (fun n=> P n i r) (Q i r))(A:PowerSeries ℝ)(i r) : Yields (fun n=> Blue.mix A (P n) i r) (Blue.mix A Q i r):=by
   unfold Blue.mix; exact (Yields.sum _ (fun j _=> (h j r).smul _)).congr (Eventually.of_forall fun n=> by rw [Finset.sum_apply]; rfl)
lemma account (g:G.Simple) (N:ℕ): Hier (freeForms A N N) (tale G) := by
    have he n: Interlace (freeForms A N N) (topW G n):= W_shape (drawTop A n N)
    have hh (i r):= scissors (P:=fun n=> sprig (eWilson (G:=G) (c:=n)) 2) (Q:=moon G) (moon_pages G i r)
    refine ⟨he,hh,?_⟩
    ext i; cases i with
    | zero=>
      have hv : Yields (fun n=> flatPal (precisionC G n (freeForms A N N)) 0 2) (orbQ (plain G (freeForms A N N))):= by simpa only [flatPal,↓reduceIte,shine_lit] using (flatY (horizon_ports A N N) 0 2)
      have ht : (lop (moon G)) 0 2=orbQ (plain G (freeForms A N N)):= (hh 0 2).unique (hv.congr (Eventually.of_forall fun n=> (congr_fun (he n).stem 2).symm))

      rw [stellar_read, show (tale G).2 0 2=_ from ht,crown_read g]; simp
    | succ i=>
      have ht : lop (moon G) (i+1) 2=0:= (hh _ _).unique (Yields.zero.congr (Eventually.of_forall fun n=> (show topW G n (i+1) 2=0 from shine_dark (by omega)).symm))
      rw [stellar_read, show (tale G).2 (i+1) 2=_ from ht,sun_zero]; simp

structure NextP (U:Mantle G) (N m:ℕ) : Prop where
  growth i r: Yields (fun n=> unripe A Ñ N m U.1 n i r) (season A Ñ N m U.2 i r)
  calm: constantCoeff (Kstar (season A Ñ N m U.2))=1
  parityC: evenC (Kstar (season A Ñ N m U.2))
  lead: season A Ñ N m U.2 0= shine (orbQ (plain G (freeForms A N m)))

lemma stirring {U:Mantle G}(g:G.Simple)(h:LocalRatio Ñ)(b:Hier (freeForms A N (m+1)) U)(p:m<N): NextP A Ñ U N m := by
    let J:= horizon_ports A N m
    let Y:= freeForms A N m; let H:= freeForms A N (m+1)
    let P:= loose A m; let K:=A.clock.kernel; let Q:= roam A N m
    have hp:P.Branches K G:= (A.blocks m 0).branches
    have he i r: Yields (fun n=> unripe A Ñ N m U.1 n i r) (season A Ñ N m U.2 i r):= raw_roll P K Ñ H Y U.1 Q hp h b.patch (resin A N m p) J i r
    have hb n: unripe A Ñ N m U.1 n 0= shine (orbQ (precisionC G n (freeForms A N m))):= winter_calm _ _ _ _ _ h
    have ht: season A Ñ N m U.2 0= flatPal (plain G (freeForms A N m)) 0:= by
       ext1 r; exact (he 0 r).unique ((flatY J 0 r).congr (Eventually.of_forall fun n=>by rw [hb]; rfl))
    have hu: season A Ñ N m U.2 0=shine (orbQ (plain G (freeForms A N m))):=ht
    refine ⟨he,by rw [← coeff_zero_eq_constantCoeff_apply, stellar_read,hu,shine_lit,crown_read g],pane_even ?_,hu⟩
    intro i r h'
    have hf n : PairP (lop (unripe A Ñ N m U.1 n)):= pair_winter _ _ _ _ _ (b.basis (n*P.L)).evenP
    exact (scissors (P:=unripe A Ñ N m U.1) (Q:=season A Ñ N m U.2) (he i r)).unique (Yields.zero.congr (Eventually.of_forall fun n=> (hf n i r h').symm))

lemma age_sym (n N':ℕ) (k:Side): ((freeForms A n N').acts k).transpose=(freeForms A n N').acts k := by
    obtain ⟨_,_,h⟩:= vacuum_positive _ A.clock.kernel.penalty_pos (A.clock.adm N'); exact (h (location A n N') k).1

lemma leap {U:Mantle G}(g:G.Simple)(h:LocalRatio Ñ)(b:Hier (freeForms A N (m+1)) U)(p:m<N): Hier (freeForms A N m) (twinkle A Ñ N m U):= by
   let P:= loose A m; let H:= freeForms A N (m+1); let Y:= freeForms A N m
   let Z:= Kstar (season A Ñ N m U.2)
   have F:= stirring A Ñ g h b p
   refine ⟨fun n=>?_,covers_mix (P:=fun n=> lop (unripe A Ñ N m U.1 n)) (Q:=lop (season A Ñ N m U.2)) (fun i r=> scissors (P:=unripe A Ñ N m U.1) (F.growth i r)) (back Z),begin_again F.calm fun i=>(F.growth i 2).cover⟩
   let S:= mStep A n m
   have ht:=horizon_step A m N p n (n*P.L) rfl
   exact reclosed S (repeatF S) H Y (roam A N m n) (A.blocks m 0).branches h (b.basis (n*P.L)) ((cond_laws A m N).1 n (n*P.L) rfl) ht (age_sym A ..) (age_sym A ..) Z F.calm F.parityC

theorem old (g:G.Simple)(h:LocalRatio Ñ)(N m:ℕ) (p:m≤N): Hier (freeForms A N m) (story A Ñ N m) := by
   suffices hf: ∀ k i:ℕ,i+k=N→ Hier (freeForms A N i) (story A Ñ N i) from hf (N-m) m (by omega)
   intro k; induction k with
   | zero=>
       intro i hi; have he:i=N:=by omega
       rw [he,story_top]; exact account A g N
   | succ k ih=> intro i hi; rw [story_stride A Ñ (by omega)]; exact leap A Ñ g h (ih (i+1) (by omega)) (by omega)
lemma perch (g:G.Simple)(h:LocalRatio Ñ)(p:m<N): NextP A Ñ (story A Ñ N (m+1)) N m:= stirring A Ñ g h (old A Ñ g h N _ p) p

-- target-facing top-degree invariants.
structure BulkP (H:FaceRow)(U:Canvas G) : Prop where
  readout : U 0= shine (orbQ (plain G H))
  signs : swing U
  rank : shellK 2 U
  grade : PairP U
  empty : lop U=U
  rise : Kstar U=1
  vanishes i: U i 1=0
  center i r: stroll (U i r)
  pureU i : Pure (U i)
  paintU : leanTwo U
  separate : vertical U
  affine i: i≠0 → Aware (U i 2)
  paid i r : ∃ σ C:ℝ,0<σ ∧ Amber terrain σ C (U i r)

theorem catchment (g:G.Simple)(h:LocalRatio Ñ)(p:m≤N): BulkP (freeForms A N m) (actionW A Ñ N m):= by
   let U:= (story A Ñ N m).1; let V:= actionW A Ñ N m
   let H:= freeForms A N m
   have e:=old A Ñ g h N m p
   have he n: Interlace H (U n):= e.basis n
   have hu i r: Yields (fun n=>U n i r) (V i r):= e.patch i r
   have ht i: Pure (V i):= fun r=> (hu i r).sym (Eventually.of_forall fun n=> (he n).shape i r)
   obtain ⟨hs,hc,hK,hF⟩:= omni g hu (fun n=>⟨_,(he n).lamp⟩) (fun n=>(he n).shape) fun n=> (he n).valid
   change BulkP H V; refine ⟨?_,hs,?_,?_,?_,e.readP,hK,fun i r=>(hu i r).road,ht,hc,hF,?_,fun i r=> (hu i r).cover⟩
   · ext1 r; apply (hu 0 r).unique; apply (flatY (horizon_ports A N m) 0 r).congr; exact Eventually.of_forall fun n=> congr_fun (he n).stem.symm r
   · intro i r hk; exact (hu i r).unique (Yields.zero.congr (Eventually.of_forall fun n=> ((he n).lamp i r hk).symm))
   · intro i r hk; exact (hu i r).unique (Yields.zero.congr (Eventually.of_forall fun n=> ((he n).evenP i r hk).symm))
   · ext1 i; ext1 r; refine (scissors (P:=U) (Q:=V) (hu i r)).unique ((hu i r).congr (Eventually.of_forall fun n=>?_)); exact congr_fun (congr_fun (he n).clear.symm i) r
   intro i hi; obtain ⟨s,a,hg,H⟩:= (hu i 2).cover
   apply aware_of_reset (spin_has hs) H hg (fun x c=>west_floor hF ht hK i x c) (loyal_medium hc); rw [← stellar_read,show Kstar V=1 from e.readP]; simp [hi]
end YM.WilsonCoeffUV.Bank
