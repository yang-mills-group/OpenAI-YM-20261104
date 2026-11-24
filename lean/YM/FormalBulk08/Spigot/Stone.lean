import YM.FormalBulk08.Spigot.Draft
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type*}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}
open Grail Precision Work.F03 Pose Tensor
open Planned.PrimaryIntegral295 Place Carrier
open scoped Matrix.Norms.Frobenius

def jetL (a:Atom G r)(n:Side)(j:ℕ) := Broc.beam (spring a (n:=n)) j
section upper
-- synthetic tensor lift
variable [Fintype I]
def sunn (d:ℕ)(x:Tor (village d) I):Biglot I:=(lift x.1,x.2)
def rivet (d:ℕ)(u: Tile (Tor (village d) I) r):Tile (Biglot I) r:= fun p=>∑ x:chain (Tor (village d) I) r, if sunn d ∘ x=p then u x else 0
omit [Fintype I] in
lemma sun_unique (d:ℕ) : Injective (sunn (I:=I) d):= LeftInverse.injective (g:=Lotus.drip _ ) (f:=sunn d) (by intro x; refine Prod.ext ?_ rfl; exact wrap_lift _)
lemma rivet_in (d)(u: Tile (Tor (village d) I) r)(x:chain (Tor (village d) I) r): rivet d u (sunn d ∘ x)=u x:= by
   unfold rivet; rw [Finset.sum_eq_single x];simp;intro a _ h; exact if_neg fun e=>h (funext fun i=> sun_unique d (congr_fun e i)); simp
lemma rivet_live (d)(T:Tile (Tor (village d) I) r)(x)(h:rivet d T x≠0):∃ v,sunn d ∘ v=x:= by
   by_contra! he; unfold rivet at h; simp_rw [if_neg (he _), Finset.sum_const_zero] at h; contradiction
lemma rivet_turn (d)(T:Tile (Tor (village d) I) r)(h:Agate T):Agate (rivet d T) := by
    intro v l;unfold rivet; let E:=Equiv.arrowCongr l.symm (Equiv.refl (Tor (village d) I)); rw [←Equiv.sum_comp E]; apply Finset.sum_congr rfl; intro x hx; have he:sunn d ∘ E x = v ∘ l ↔ sunn d ∘ x=v:=⟨fun e=>funext fun j=>by simpa only [E,Equiv.arrowCongr_apply, comp_apply, Equiv.refl_apply,Equiv.symm_symm, l.apply_symm_apply] using congr_fun e (l.symm j),fun e => by rw [←e];rfl⟩; by_cases hp:sunn d ∘ x=v; rw [if_pos hp,if_pos (he.2 hp)];exact h x l
    rw [if_neg hp,if_neg (hp ∘ he.1)]
lemma rivet_gate (d) (T:Tile (Tor (village d) I) r): sieve n (rivet d T)=cores (Lotus.drip n ∘ sunn d) T:= by
    funext v; rw [sieve_i, cores_here]; unfold rivet
    let R:= Lotus.drip n ∘ sunn (I:=I) d; let U:=Tor (village d) I
    let M (a:chain U r) (x:chain (Biglot I) r) := if R ∘ a=v ∧ sunn d ∘ a=x then T a else 0
    have ht(x:chain (Biglot I) r): (if Lotus.drip n ∘ x=v then (∑ a:chain U r,if sunn d ∘ a=x then T a else 0) else 0)=∑ a,M a x:= by
       by_cases hh:Lotus.drip n ∘ x=v; swap
       · rw [if_neg hh,eq_comm]; apply Finset.sum_eq_zero;intro a _; exact if_neg (fun ⟨hx,hb⟩=> hh (hb ▸ hx))
       rw [if_pos hh]; apply Finset.sum_congr rfl; intro i _; by_cases he:sunn d ∘ i=x;rw [if_pos he];exact (if_pos (And.intro (show R ∘ i=v from (show Lotus.drip n ∘ (sunn d ∘ i)=v by rw [he,hh])) he): M i x=T i).symm
       simp [M,he]
    refine ((tsum_congr (fun i: chain (Biglot I) r=>ht i))).trans ?_; have he(a:chain U r):∀ i, i≠ sunn d ∘ a→ M a i=0:= fun i hi=> if_neg fun h=> hi h.2.symm
    rw [Summable.tsum_finsetSum (s:=Finset.univ) (f:=M) (fun i _=>summable_of_ne_finset_zero (s:={sunn d ∘ i}) (fun x hx=> he i x (by simpa using hx)))]; apply Finset.sum_congr rfl; intro i _; rw [tsum_eq_single _ (he i)]; unfold M; simp only [eq_self,and_true];congr 1
omit [Fintype I] in
lemma rivet_home (o:I)(d:ℕ)(x:chain (Tor (village d) I) r) : herb (fame _) (0,o) (sunn d∘ x)≤8*d:= by
   let y : chain (Biglot I) (r+1):=Fin.cons (0,o) (sunn d ∘ x); have ht i:size (y i).1≤4*d:= by
        cases i using Fin.cases
        · simp [y,Laurent.size]
        next i=> exact farsum (x i).1
   refine known_wide _ _ _ fun i j=>?_ ; change size ((y i).1-(y j).1)≤_; rw [sub_eq_add_neg]; apply (size_add ..).trans;rw [size_neg]; have hp:=ht i; have he:=ht j; omega
end upper
lemma jet_comp (a:Atom G r)(n:Side)(j:ℕ): sieve n (rivet a.length (I:=Loc G 1) (jetL a _ j))=jetL a n j:= by
    let d:=a.length; let m:=village d;let k:= Lotus.drip n ∘ sunn (I:=Loc G 1) d; let S:= spring a (n:=m)
    rw [rivet_gate, jetL,jetL,Broc.beam_seed _ (spike _).analyticAt, Broc.beam_seed _ (spike _).analyticAt, ←Shore.pebble]; refine congr_arg _ (?_ : MvPolynomial.rename k _=_)
    have he : spring a (n:=n)= S ∘ (fun (x:Link G n)=>x ∘ k) := by
       have h:=Stationary.inhabit d (aTerm a) (aTerm_at a) (0:Site n); refine Eq.trans h (?_); apply congr_arg; funext p i; simp [patchCopy,k,sunn, Lotus.drip]
    rw [he, paste_steps S (fun x:Link G n=> x ∘ k) ((spike a).of_le le_top) (contDiffAt_pi.mpr fun i=>contDiffAt_apply ..) rfl, fit_translate, coeff_map];rfl
-- point and width
lemma cap_delta (v:chain (wire G n) r)(i): ‖axes (dotI (v i):Jets.Rays _)‖≤ 1:= by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun a=>?_ ; unfold axes dotI;by_cases h:a=v i <;> simp [h]
lemma spring_jet_price {π R:ℝ}(a:Atom G r)(hp:VaultOn G (aTerm a) R π)(h:0<R)(v:chain (wire G n) t): ‖jetL a n t v‖≤costNote t R*π:= by
    obtain ⟨g,hg,hv,ht⟩:=hp n 0; change g ∘ axes=Complex.ofRealCLM ∘ (spring a (n:=n)) at ht
    let Q:=dotI ∘ v
    have hE:0≤π:= (norm_nonneg _).trans (hv _ (Metric.mem_ball_self h))
    rw [←Complex.norm_real, show (↑(jetL a n t v):ℂ)= noteAt (spring a) t (axes ∘ Q) from (note_real (spring a (n:=n)) Q).symm]; refine (mixtape_cost h hg hv ht t (axes ∘ Q)).trans ?_
    have he : (∏ i,‖axes (Q i)‖) ≤ 1:= by simpa only [Finset.prod_const_one] using Finset.prod_le_prod (s:=Finset.univ) (f:=fun i=>‖axes (Q i)‖) (fun _ _=>norm_nonneg _) (fun i _=>cap_delta v i)
    exact (mul_le_of_le_one_right (mul_nonneg (by positivity) (mul_nonneg hE (circleTax_pos h t).le)) he).trans_eq (by unfold costNote; ring)

def flame (a:Atom G r)(j:ℕ):Tile (edgeL G) j:=rivet a.length (jetL a _ j)
lemma flame_low (a:Atom G r)(h:t<r): flame a t=0:= by
   have he : jetL a (village a.length) t=0:= by rw [jetL,Broc.beam_seed _ (spike _).analyticAt,springLow _ _ t h]; apply _root_.YM.FormalBulk08.Lava.marble_zero
   unfold flame; rw [he];funext v; simp [rivet]
lemma flame_register (a:Atom G r)(t:ℕ) : Agate (flame a t):= rivet_turn a.length _ (Broc.beam_pulse _ (spike _).analyticAt t)
lemma rub (o:Loc G 1)(t r:ℕ)(hs:0<σ) : ∃ η C:ℝ,0<η∧0≤C∧ ∀ a:Atom G r, Knoxville (fame _) η (0,o) (flame a t) ((a.budget σ)*C):= by
    obtain ⟨R,h,H⟩:= term_vault G (show 0<σ/2 from half_pos hs)
    let η:= σ/32;have he:0<η:=by unfold η; positivity
    obtain ⟨K,hk,J⟩:= cut_barn (r:=t) o (show η<2*η by linarith)
    let M:= costNote t R* |Work.F02.slotConst G ^ r|
    have hm:0≤ M:= mul_nonneg (note_pos h) (abs_nonneg _); refine ⟨η,K*M,he,mul_nonneg hk hm,fun a=>?_⟩
    have hp v: ‖flame a t v‖ ≤ (M*a.budget σ)*Real.exp (-(2*η)*herb (fame _) (0,o) v):= by
        have hx:0≤ a.magnitude:= Finset.sum_nonneg fun _ _=>abs_nonneg _; by_cases hz:flame a t v=0
        · rw [hz,norm_zero]; unfold Atom.budget; positivity
        obtain ⟨x,rfl⟩:=rivet_live _ _ _ hz; unfold flame; rw [rivet_in]
        refine (spring_jet_price a (H _ a) h x).trans ?_
        let d:ℝ:=a.length; let D:ℝ:= herb (fame _) (0,o) (sunn a.length ∘ x)
        have ht : D≤8*d:= by unfold D d; exact_mod_cast rivet_home o a.length x
        have ha : Real.exp (σ/2*d)≤Real.exp (σ*d)*Real.exp (-(2*η)*D):= by
            rw [←Real.exp_add]; apply Real.exp_monotone;dsimp only [η]; nlinarith [mul_le_mul_of_nonneg_left ht hs.le]
        have hr:0≤ a.budget (σ/2):= mul_nonneg hx (Real.exp_pos _).le
        refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self (Work.F02.slotConst G^r)) hr) (note_pos h)).trans ?_
        change costNote _ _ *(a.budget _*|_|) ≤ _
        rw [mul_comm (a.budget (σ/2)),←mul_assoc]; change M*(a.magnitude * Real.exp (σ/2*d)) ≤ M*a.budget σ*_; rw [←mul_assoc M]
        exact (mul_le_mul_of_nonneg_left ha (mul_nonneg hm hx)).trans_eq (by unfold Atom.budget d D; ring)
    rw [mul_comm (a.budget σ),mul_assoc]; exact actual_penn (J _ _ (mul_nonneg hm (by unfold Atom.budget Atom.magnitude; positivity)) (fun i=>norm_nonneg _) hp)
end YM.FormalBulk08.Spigot
