import YM.Qlocal.Regular
import YM.Qlocal.Versal.Cactus
import YM.RGComparison01.Marks.Luggage
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal
open Filter Function Lattice RG Wilson Finset MeasureTheory Matrix
open Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel
  Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03
  Animals Control Window Coat Footprint Pulse Itinerary Blaze Scroll Vine Polar Frond
  Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas
  Ursell Trees Height Sail PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open RGComparison01 RGComparison01.Pledge Checks Foreman Baked Palette Pillow Resin Season March
variable {G : Gauge} {ι Ω : Type} {c f L : Side} {S : StepData c f}
    {P : Teller G} {T : Tube G S} {R : RG.Rep G f}
    {W β μ C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
    {H : Cash W β μ L Q o C T R} {d r a e b kα δ : ℝ} {n j : ℕ} {χ : Chi}

-- A single physical layout of real (not complexified-coupling) tails.
-- Note that we never require a different vacuum or a different label space at each test.
variable {M : ι → Leaf R} {D : Ω → ι → Leaf R}
open RGComparison01 RGComparison01.Pledge Stowe
namespace Roster
variable (H) (h:Roster M D)
local notation "J"=> h.castLabel H
-- geometry and cut indices across all kernels on tests. Store cutoff chosen ONCE for all queries even if jut singular because cast.C.Frame.L
lemma record (p:Cl M H)(x:Ω): recordSet (D x) H (J x p)=recordSet M H p:=rfl
lemma season (p:Cl M H)(x:Ω)(z:Option (Fin p.1)) : Season.sand (M:=D x) ((J x p).2 z)=Season.sand (p.2 z):= congr_arg ((p.2 z).1.val \ ·) (h.signs_eq x ((p.2 z).2)) -- args.T.ToInt.
lemma condition {a:ℕ→Prop} (p:Cl M H)(x:Ω): Season.Ode a (J x p) ↔ Season.Ode a p:= by unfold Season.Ode Season.ocean; simp_rw [h.season]; rfl
lemma winter (m:ℕ)(p:Cl M H)(x:Ω): Season.Heavy m (J x p) ↔ Season.Heavy m p := by
 have he : Season.age (J x p)= Season.age p:=by unfold Season.age; apply Finset.sum_congr rfl; intro i _; rw [h.season]
 unfold Season.Heavy; rw [he]; unfold Season.scare; simp_rw [h.season]; rfl
variable {μ' : Type}{b':ℕ} (I:Cabinet μ' H b') [Fintype ι]
lemma file (p:Cl M H)(q:Finset ι)(x:Ω)(k m:ℕ): J x p ∈ ledger (D x) H I k m q ↔ p∈ledger M H I k m q := by
 have hp:Canyon.pattern (J x p)= Canyon.pattern p:= rfl; unfold ledger; rw [mem_filter, mem_filter, Stowe.posted, Stowe.posted,hp]; unfold struck; refine and_congr_right fun h0=> Iff.and Iff.rfl ?_; change (∀ i:Option (Fin p.1),(Roster.tickets (S:=S) h x ((p.2 i).2)).reach ⊆ (p.2 i).1.val) ↔ _; simp_rw [h.signs_eq]
end Roster
open Baked Palette Pillow Heron
namespace UniformRooted
variable {α: Type} {U : α→ Support c}{f g: Ω→ α→ Config G c→ℝ} {p: BudgetPoint}
open Quipu.Sonnet
local notation "Φ"=> (Config G c→ℝ)
lemma disj (h:UniformRooted U f p a b)(h0:∀ i x, g x i=f x i∨g x i=0): UniformRooted U g p a b:= by
 obtain ⟨d,hd,hD⟩:= h.majorize; refine ⟨d,fun i=> ⟨(hd i).1,fun x=>?_⟩,hD⟩; rcases h0 i x with he|he <;> rw [he]; exact (hd i).2 x; let V:=PayR.enlarge (PayR.zero p G (U i)) ((hd i).1); exact ⟨V.genuine,V.statement⟩ -- cannot infer
protected lemma joined (h:UniformRooted U f p a b)(h':UniformRooted U g p a d):UniformRooted U (f+g) p a (b+d):= by
 obtain ⟨c,hc,he⟩:= h.majorize; obtain ⟨d,hd,hQ⟩:=h'.majorize; refine ⟨c+d,fun i=> ⟨add_nonneg (hc i|>.1) (hd i|>.1),fun x=>?_⟩,?_⟩
 · let V:PayR p (U i) (c i+d i) (f x i +g x i):= PayR.add ⟨(hc i).1,((hc i).2 x).1,((hc i).2 x).2⟩ ⟨(hd i).1,((hd i).2 x).1,((hd i).2 x).2⟩; exact ⟨V.genuine,V.statement⟩
 intro i; convert budget_plus (he i) (hQ i) using 1; ext j; split_ifs <;> simp [add_mul, *]
-- true.Tsup family. adapted `Rooted.fadings`.
lemma retire (h:UniformRooted U f p a b)(Q:ℕ→α→Prop)(hQ:∀ x i, f x i≠0→ ∀ᶠ n in atTop,¬ Q n i)(he:0 < e) : ∀ᶠ n in atTop,UniformRooted U (fun x i=>if Q n i then f x i else 0) p a e:= by
 obtain ⟨v,hv,Hv⟩:=h.majorize; let u n i:= if Q n i∧∃ x,f x i≠0 then v i else 0; have hu n i:0≤u n i:=by unfold u; split; exact (hv _).1;rfl
 let g n x i:= if x∈U i then u n i*Real.exp (a*coverNumber p.B (U i)) else 0; let g0(x:Site c) i:= if x∈U i then v i*Real.exp (a*coverNumber p.B (U i)) else 0; have hg (n:ℕ)(x:Site c) i:0≤g n x i:= by unfold g; split; exact mul_nonneg (hu _ _) (Real.exp_nonneg _); rfl
 have hs n x i:g n x i ≤ g0 x i:= by unfold g g0 u; split_ifs; rfl; rw [zero_mul]; exact mul_nonneg (hv _|>.1) (Real.exp_nonneg _);rfl
 have hw(x:Site c):∀ᶠ n in atTop, SumBudget (g n x) e:= by
    have ht : Tendsto (fun n=>∑' i,g n x i) atTop (𝓝 0):= by
       have hp(i:α): Tendsto (fun n=>g n x i) atTop (𝓝 0):= by
         unfold g; split_ifs; swap; · exact tendsto_const_nhds
         by_cases h:∃ x,f x i≠0; swap; · exact tendsto_const_nhds.congr (by intro; simp only [h,u,and_false,if_false,zero_mul])
         obtain ⟨x',hv⟩:=h; exact tendsto_const_nhds.congr' ((hQ x' i hv).mono (fun n hn=>by simp only [hn,u,false_and,if_false, zero_mul])) -- split_ifs also inner? 
       have hf:= tendsto_tsum_of_dominated_convergence (show Summable (g0 x) from (Hv x).2.1) hp (Eventually.of_forall fun n i=> by rw [Real.norm_of_nonneg (hg n x i)]; exact hs ..); rwa [tsum_zero] at hf
    exact (ht.eventually_le_const he).mono (fun n hn=> ⟨hg n x,(Hv x).2.1.of_nonneg_of_le (hg n x) (hs n x),hn⟩)
 filter_upwards [eventually_all.mpr hw] with n hn; refine ⟨u n,fun i=>⟨hu n i,fun x=>?_⟩, hn⟩; by_cases h:f x i≠0∧ Q n i; · unfold u; rw [if_pos h.2, if_pos ⟨h.2,⟨x,h.1⟩⟩]; exact (hv i).2 x
 let V:= PayR.enlarge (PayR.zero p G (U i)) (hu n i); rw [show (if Q n i then f x i else 0)=0 by split; exact not_not.mp (fun hv=> h ⟨hv,‹_›⟩);rfl]; exact ⟨V.genuine,V.statement⟩
end UniformRooted
namespace Surveyor
open Baked Palette Luggage Season
variable (H) (g:ι→ℝ)(h:Roster M D)(χ:Chi)(p:BudgetPoint)(R':Ribbon R n) (t: Finset ι→ Prop)
set_option quotPrecheck false
local notation "μ"=> entry H h g χ
local notation "Ψ"=> crop H h g
local notation "z"=> h.castLabel H
local notation "T★"=>recordSet M H
local notation "O"=> origins M H
local notation "Y"=> Drawing.cabinet H R'
variable [Fintype ι]{d' r':ℝ} {E:ℕ→Prop} (η:ℕ) (hT:Drawing.Opens R' E)
local notation "hL"=> UniformRooted O
include hT
lemma missing (hp: ∀ p,t p→ ∀ i∈p,¬ Luggage.long M R' i) (h0:UniformRooted O μ p a b)
  (h1: UniformRooted O (Ψ (fun i=> Season.Heavy j i ∧ ¬Ode E i) χ) p a kα)
  (h2: UniformRooted O (Ψ (Ode E) χ) p a δ)(he:0 < e) : ∀ᶠ m in atTop, UniformRooted O (Ψ (fun i=> Luggage.miss M H R' η (j+η) m i ∧ t (T★ i)) χ) p a (δ+kα+e):= by
 let F m i:= Luggage.miss M H R' η (j+η) m i∧ t (T★ i);
 let F0 m i:= F m i∧ Ode E i; let F1 m i:= F m i ∧ (Season.Heavy j i ∧ ¬Ode E i); let f3 m i:= F m i∧ ¬(Season.Heavy j i ∧ ¬Ode E i)∧¬Ode E i
 have h3:∀ᶠ m in atTop, hL (Ψ (f3 m) χ) p a e:= by
    refine h0.retire f3 ?_ he; intro x i hi; by_cases hx : Luggage.core M H η i∧ t (T★ i)∧ ¬Season.Heavy j i ∧ ¬Ode E i; swap; · exact Eventually.of_forall fun m ⟨⟨⟨hn,hr⟩,ht⟩,h0,h2⟩=> hx ⟨hn,ht,fun hf=> h0 ⟨hf,h2⟩,h2⟩
    let p':= T★ i; obtain ⟨h₀,h₁,hM,hK⟩:= hx; obtain ⟨y,hy⟩:∃ V: Config G c,μ x i V ≠0:= not_forall_not.mp (fun h'=>hi (funext fun V=> not_not.mp (h' V))); let t:=D x; -- `z` may conflict no blocker
    have hl : ∀ j∈p',∀ k,(D x j).turn= Lotus.Wing.logKey k→ R'.keep k:= fun j hj k hk=>Classical.byContradiction fun ht=> hp _ h₁ j hj ⟨k, (h.turns x j).symm.trans hk,ht⟩
    filter_upwards [Stowe.lowRibbon (D x) g H p' (z x i) R' E hT hl y ⟨rfl,h₀.2.2⟩ (χ:=χ) hy (mt ((h.winter H j i x).mp) hM) (mt ((h.condition H i x).mp) hK) η (h₀.2.2.symm ▸ h₀.2.1)] with m hm; exact fun hf=> hf.1.1.2 ((h.file ..).1 hm) -- h₀.rewrite sym orientation
 filter_upwards [h3] with m hv
 have hx: hL (Ψ (F0 m) χ) p a δ:= h2.disj (by intro i x; unfold crop; by_cases hw:F0 m i; rw [if_pos hw,if_pos hw.2]; exact Or.inl rfl; exact Or.inr (if_neg hw))
 have hy: hL (Ψ (F1 m) χ) p a kα:= h1.disj (by intro i x; unfold crop; by_cases hn:F1 m i; rw [if_pos hn,if_pos hn.2]; exact Or.inl rfl; exact Or.inr (if_neg hn))
 let U:= hx.joined hy |>.joined hv; refine Eq.mp ?_ U; congr 1; ext x i V; change ((Ψ (F0 m) χ x i + Ψ (F1 m) χ x i)+ Ψ (f3 m) χ x i) V= Ψ (F m) χ x i V; by_cases hn: F m i <;> by_cases he: Season.Heavy j i <;> by_cases hE: Ode E i <;> simp only [crop,F0,F1,f3, Pi.add_apply, Pi.zero_apply, he,hn,hE, not_false_eq_true, ↓reduceIte, not_true, true_and, false_and, and_false,add_zero, zero_add]
end Surveyor
end YM.Qlocal
