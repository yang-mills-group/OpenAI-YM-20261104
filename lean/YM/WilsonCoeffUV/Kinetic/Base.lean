import YM.WilsonCoeffUV.Kinetic.Momentum
/-!
# Reclosure hooks for comparing P front from Kin
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Near Stationary PowerSeries Roam Asymptotics Tree Supply Next.Free
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{s C B:ℝ}{R:PathData G}{u: Clip}{e m N:ℕ}
variable {A:Levels G}{Ñ:ChartRatio G}

lemma period_crumb (A:Levels G)(m:ℕ):Tendsto (A.S.side m) atTop atTop:=by
    have he:StrictMono (fun p=> (A.S.side m p).val):=by
       intro i j h; change ((A.S.period i).val * _ :ℕ)< (A.S.period j).val*(A.S.denominator m).val; exact Nat.mul_lt_mul_of_pos_right (A.S.period_strict h) (A.S.denominator m).pos
    refine tendsto_atTop.2 (fun v:Side=>?_); exact he.tendsto_atTop.eventually (eventually_ge_atTop v.val)
lemma seam_power (h: LocalRatio Ñ)(hp:G.Simple) (v:R.Bounds u s C B)(p:m≤ N)(t: SeamPhase u R (actionW A Ñ N m)) (n:Side):
    front R u n 0=shine (orbQ (precisionC G n (freeForms A N m))):=by
    have hs := catchment A Ñ hp h p
    ext1 j; cases j with
    | zero=>rw [front_full v n]; simp_rw [Pi.add_apply,Pi.smul_apply, sprig]; rw [shine_dark (by omega), sands_zero_v, smul_zero,zero_add,shine_dark (by omega)]
    | succ j=>
       rw [frontr v 0 j n,t.low 0 (by omega),hs.readout]
       by_cases he:j=1; subst j; change lagoon (Blue.shine (orbQ (plain G (freeForms A N m))) 2) n=Blue.shine _ 2; rw [shine_lit,shine_lit]
       · obtain ⟨s,A',hS,ht,hT⟩:= forms_tail A.clock.kernel.penalty A.clock.kernel.penalty_pos _ (A.clock.adm m)
         exact plain_act G n ((hT A m rfl rfl).1 N) hS.le
       rw [shine_dark (by omega),shine_dark (by omega), lagoon_none]
-- locality in order for season
lemma same_tide {U:Type}{P Q:Pal ℝ (Cloth U)}(h:∀ i≤ m,P i=Q i)(K:ropes Cover U U)(i j:ℕ)(p:j≤m): tide K P i j=tide K Q i j:=by
    induction i using Nat.strong_induction_on generalizing j with
    | h i ih=> cases i with
       | zero=> rw [tide_zero,tide_zero,h j p]
       | succ i=>
          rw [tide_rise,tide_rise, ih i (by omega) j p]; unfold curlJ; congr 2; apply Finset.sum_congr rfl; intro x hx; apply Finset.sum_congr rfl; intro y hy
          have h:= Finset.mem_antidiagonal.mp hx; have hz:= Finset.mem_antidiagonal.mp hy
          rw [ih x.1 (by omega) y.1 (by omega),ih x.2 (by omega) y.2 (by omega)]
lemma season_stave (A:Levels G)(Ñ:ChartRatio G)(N m0:ℕ) {P Q:Canvas G}(h:∀ i≤ m,P i=Q i)(i)(he:i≤m): season A Ñ N m0 P i=season A Ñ N m0 Q i:=by
    unfold season tinge; simp only [Pi.add_apply,Pi.sub_apply]; unfold snow; congr 3
    apply Finset.sum_congr rfl; intro j _; apply same_tide _ _ _ _ he
    intro y hy; unfold stellar; simp only [Pi.sub_apply, scrub, h y hy]
lemma stanza (K:R.Bounds u s C B)(h:LocalRatio Ñ)(p:m<N)(z:SeamPhase u R (actionW A Ñ N (m+1)))(i r:ℕ)(v:i<3):
    Yields (fun n=> unripe A Ñ N m (fun n=>front R u n) n i r) (freshet A Ñ N m i r):=by
    have he:=raw_roll (loose A m) A.clock.kernel Ñ (freeForms A N (m+1)) (freeForms A N m) (fun n=>front R u n) (roam A N m) (A.blocks m 0).branches h (breast_turn K) (resin A N m p) (horizon_ports A N m) i r
    change Yields _ (season A Ñ N m (breast R u) i r) at he
    rw [season_stave A Ñ N m (fun i (t:i≤2)=>z.low i (by omega)) _ (by omega)] at he; exact he

lemma front_paths (_K:R.Bounds u s C B)(n:Side)(i:ℕ): front R u n i (2+i)=rye (intended u R) (2+i):=by
    rw [front]; simp only [Pi.add_apply, sprig,shine_lit]; rw [shine_dark (by omega),add_zero]
lemma front_span (K:R.Bounds u s C B) (i j)(h: j≠ 2+i)(e:j≠ i): breast R u i j=0:=
    (breast_turn K i j).unique (Yields.zero.congr (Eventually.of_forall (fun n=>by simp only [front,Pi.add_apply,sprig, zero_add,shine_dark h.symm,shine_dark (show 0+i ≠ j by omega)]; simp)))
-- top matches prior. use cofinal side, all ranks, Wilson near fields
variable {H:Horizon A}{P:Kin H Ñ}{s0: Sheet G}{R0 : Rolls s0}{B': PostCost R0}
lemma dawns (h:P.Planned B')(N p:ℕ)(i:ℕ)(u:i≤4) : rye (intended (A.params N).clip (P.path N N) (m:=A.S.side N p)) i= rye eWilson i:=by
    rcases h.peak N p i u with ⟨a,b,c⟩; let n:= A.S.side N p
    let X (u:fieldDir G n 1):=mainTerm (A.params N).clip (P.path N N) (represent u); let v (u:fieldDir G n 1):=Wilson.energy (represent u); let L:=(arm G n 1).toContinuousLinearMap
    change rye (X ∘ L) i= _; funext u; unfold rye; change _ = _ • iteratedFDeriv ℝ _ (v ∘ L) 0 _; rw [wired L ?_,wired L ?_,map_zero,show iteratedFDeriv ℝ i X 0=iteratedFDeriv ℝ i v 0 from c]
    all_goals rw [map_zero]
    exacts [b.analyticAt,a.analyticAt]
lemma breast_top (h:P.Planned B')(N:ℕ): SeamPhase (A.params N).clip (P.path N N) (actionW A Ñ N N) :=by
    let C:=(A.params N).clip; let Q:=P.path N N
    have he:=h.cap N N le_rfl
    constructor; intro i hi; rw [actionW,story_top]
    ext1 j; change breast Q C _ _= lop _ _ _; unfold lop; split
    next hj=>subst j; exact breast_nil he i 0 (by omega)
    next hm=>
      obtain ⟨j,rfl⟩:= Nat.exists_eq_succ_of_ne_zero hm; let W n:=front Q C n
      funext x; let X:= A.S.side N
      have hz := ((breast_turn he i (j+1)).point x).comp (period_crumb A N)
      have hf : Tendsto (fun k=> W (X k) i (j+1) (foldUnder (X k) ∘ x)) atTop (𝓝 (breast Q C i (j+1) x)):=hz
      have hx:= ((moon_pages G i (j+1)).point x).comp (period_crumb A N)
      have he (n:Side) : turnSeries Q.loop (m:=n)=0:=by funext v; simp [turnSeries,uncut,Atom.unmasked,Atom.poly,Q,h.initial,Patch.average]
      apply tendsto_nhds_unique hf; refine (hx.congr fun v=>?_)
      simp only [Function.comp_apply,dilute,Nat.succ_ne_zero,↓reduceIte]; unfold W C X front; simp only [Pi.add_apply]; unfold sprig; rw [show rye (intended _ Q (m:=A.S.side N v)) (2+i)=_ from dawns h N v (2+i) (by omega),he];
      rw  [show rye (0:Link G (A.S.side N v)→ℝ) (0+i)=0 from ?_]; simp [Blue.shine]
      funext v; rw [rye]; simp
end YM.WilsonCoeffUV.Bank.Mosaic
