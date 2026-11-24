import YM.SchemeRG11.Air.Kit
/-! Projection onto finitary feathers has full priced normalization,
 no inverse uniform over m. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Air
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn
open Labels Long
open scoped Classical Pointwise
variable {G:Gauge}{m n:ℕ}{T:Align.Itinerary}{R:ℝ}
def Rolling (T: Itinerary)(n:ℕ)(f:Waves):Prop:=∀ a:Axis,∀s:Fliers,s.card<n → Finishes (fun i=> T.gap i^ (-(s.card+1:ℤ))* fleet s (f i a) 0)
lemma insured(n:ℕ){f:Waves}(hp:R>0)(h:brittle T R f)(he:keeps T R f)(ht:Rolling T n f): ∃ g:ℕ→team ℝ n, Rolling T n (fun i=>(g i).val)∧∀ a s,Local T R (n+1) ((n:ℤ)-s.card) (fun i=> fleet s (f i a-(g i).val a)) :=by
 obtain ⟨g,U⟩:= lands n hp h he; refine ⟨g,fun a s hs=>?_,U⟩
 have hh:= Finishes.of (weaken_less (p:=-(s.card+1:ℤ)) (noted (U a s) hp 0) (by omega))
 apply ((ht a s hs).sub hh).same; filter_upwards with i; rw [map_sub,Pi.sub_apply]; ring
abbrev Carton(n:ℕ):=Axis × Sym Axis n
def flag(n:ℕ): Bevy ℝ→ₗ[ℝ](Carton n→ℝ):=LinearMap.pi fun p=> LinearMap.proj 0 ∘ₗ fleet p.2.val ∘ₗ LinearMap.proj p.1
lemma landed0(f:Bevy ℝ)(h:f∈team ℝ m):flag m f=0:= funext fun k=>by
 change fleet k.2.val (f k.1) 0 =_; rw [member.mp (team_wing h _) _ k.2.property];rfl
lemma lanai(f:Bevy ℝ)(h:f∈team ℝ (m+1))(H:flag m f=0): f∈team ℝ m:=by
 refine ⟨in_hull.mpr (fun i s hs=>?_),h.2⟩; funext x
 exact (landed (member.mp (team_wing h i)) _ hs x 0).trans (congrFun H (i,(⟨s,hs⟩:Sym Axis m)))
def floatR(n:ℕ): (Tail n→ℝ)→ₗ[ℝ] Bevy ℝ where
 toFun c:=∑ i,c i • (tuft i).val
 map_add' c d:=by simp [add_smul, Finset.sum_add_distrib]
 map_smul' c d:=by simp [Finset.smul_sum,smul_smul]
lemma aspir(n:ℕ):∃ L:(Carton n→ℝ)→ₗ[ℝ](Tail n→ℝ),∀f:Bevy ℝ, f∈team ℝ (n+1) → f-floatR n (L (flag n f))∈team ℝ n:=by
 let R:= flag n ∘ₗ floatR n; obtain ⟨P,H⟩:=wearer R; refine ⟨P,fun f h=>?_⟩
 have ht(c:Tail n→ℝ): floatR n c∈team ℝ (n+1):=by change ∑i,c i • (tuft i).val ∈ _; exact Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ (c i) (tuft i).property
 obtain ⟨q,U⟩:=gust n f h; have hi: flag n f= R q:=sub_eq_zero.mp ((map_sub (flag n) f (floatR n q)).symm.trans (landed0 _ U))
 apply lanai _ (Submodule.sub_mem _ h (ht _))
 rw [map_sub,sub_eq_zero,hi]; exact Eq.symm (LinearMap.congr_fun H q)
lemma liftL {I:Type*}[Fintype I]{f:ℕ→I→ℝ}(L:(I→ℝ)→ₗ[ℝ] ℝ)(h:∀i:I,Finishes (fun k=>f k i)): Finishes (fun j=> L (f j)):=by
 have H:=tendsto_pi_nhds.mpr (show ∀i:I,Tendsto ((fun k=> f k i)) atTop (𝓝 ((h i).choose)) from fun i=>(h i).choose_spec); refine ⟨_, L.continuous_of_finiteDimensional.continuousAt.tendsto.comp H⟩
lemma lift_off (m:ℕ){f:Waves}(h:∀i,f i∈ team ℝ m)(he:Rolling T m f){n:ℕ}(hn:m≤n):∃ c:ℕ→ Feather n→ℝ,(∀ i,Finishes (fun k=> c k i)) ∧∀ i, f i=∑ b:Feather n,((T.gap i)^((degree b:ℕ):ℤ)*c i b) • finch b:=by
 induction m generalizing f with
 | zero=>
   refine ⟨0,fun i=>Finishes.const (0:ℝ),?_⟩; intro i; simp only [Pi.zero_apply,mul_zero,zero_smul,Finset.sum_const_zero]; funext a; have H:=team_wing (h i) a; rw [groundZero] at H; exact H
 | succ m ih=>
    obtain ⟨P,H⟩:= aspir m; let A(i:ℕ):=P (flag m (f i)); let g(i:ℕ):= f i-floatR m (A i)
    have hw : ∀ i,g i ∈ team ℝ m:=fun i=> H _ (h i)
    let c(i:ℕ)(p:Tail m):= (T.gap i)^(-(m+1:ℤ))* A i p
    have hc(b:Tail m):Finishes (fun i=>c i b):=by
       let H:(Carton m→ℝ)→ₗ[ℝ]ℝ:=LinearMap.proj b ∘ₗ P
       let t(i:ℕ):= (T.gap i)^(-(m+1:ℤ)) • flag m (f i)
       have ht(b:Carton m):Finishes (fun i=>t i b):=by have hi:=he b.1 b.2.val (by rw [b.2.property]; omega); rw [b.2.property] at hi; exact hi
       apply (liftL H ht).same; filter_upwards with k; change H (_ • _)=_; rw [map_smul];rfl
    have cp(i:ℕ)(b:Tail m): A i b= T.gap i^(m+1:ℤ)*c i b:=by unfold c; rw [←mul_assoc,zpow_neg,mul_inv_cancel₀ (zpow_pos (T.positive i) _).ne',one_mul]
    have cg:Rolling T m g:=by
       intro a s hs;
       let k:= (s.card+1:ℤ)
       let z(b: Tail m):=fleet s ((tuft b).val a) 0
       let q:= latch T ((m+1:ℤ)-k)
       have hk:(m+1:ℤ)-k≥0:=by unfold k; omega
       apply ((he a s (by omega)).sub (Finishes.sum (f:=fun b: Tail m=> fun i=> q i * c i b*z b) Finset.univ (fun b _=> ((higher _ hk).mul (hc b)).mul (Finishes.const _)))).same
       filter_upwards with i
       change _ - (∑ _,_) = T.gap i^(-k)*fleet s (g i a) 0
       unfold g; simp only [Pi.sub_apply, map_sub,Pi.sub_apply,mul_sub]; congr 1
       unfold floatR; simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, map_sum, map_smul, Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
       apply Finset.sum_congr rfl; intro j _; rw [cp]; unfold q z latch; rw [zpow_sub₀ (T.positive _).ne',zpow_neg,div_eq_mul_inv]; ring

    obtain ⟨b,t,L⟩:=ih hw cg (by omega)
    let e: Fin n:= ⟨m,hn⟩
    let r(i:ℕ)(k:Feather n):=Pi.single (M:=fun j:Fin n=>Tail j.val→ℝ) e (c i) k.fst k.snd
    refine ⟨b+r,?_,fun i=>?_⟩
    · rintro ⟨u,d⟩; apply (t _).add; by_cases h:u=e
      · subst u; exact (hc d).same (Eventually.of_forall (fun i=>by change _=r _ _; unfold r; rw [Pi.single_eq_same]))
      exact (Finishes.const (0:ℝ)).same (Eventually.of_forall (fun i=>by change _=r _ _; unfold r; rw [Pi.single_eq_of_ne h]; rfl))
    simp_rw [Pi.add_apply,mul_add,add_smul,Finset.sum_add_distrib]; rw [←L i]; change _=g i+_; rw [show g i= f i-_ from rfl]; apply Eq.symm; convert sub_add_cancel (f i) _ using 2
    rw [Fintype.sum_sigma,Finset.sum_eq_single e]; change _=∑ k:Tail m, A i k • _;apply Finset.sum_congr rfl; intro k _; unfold r; rw [Pi.single_eq_same,cp];rfl
    · intro q h h'; apply Finset.sum_eq_zero; intro w _; simp [r,Pi.single_eq_of_ne h']
    simp
end YM.SchemeRG11.Air
