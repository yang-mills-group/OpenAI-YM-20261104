import YM.FormalBulk08.Broc.Scab

/-!
A uniform inverse, even without horizontality. Turns path bills
into bills for *all* generated higher log vertices. No formal field
sources or global ultraviolet derivatives are assumed.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Broc
open Function Filter Lattice RG Laurent Bloch Exterior
open Reef Lava Gorge Mesa Shore Lotus Wick Series Jets PowerSeries
open Stationary hiding shine Rays
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {I:Type}{G:Gauge}{n:Side}{t r:ℕ}{A σ:ℝ}

section coefficients
variable [Fintype I]
def beam (f: Jets.Rays I→ℝ)(r:ℕ): Tile I r:= fun v=> Tensor.coeff f r 0 (dotI ∘ v)
lemma beam_price (f: Jets.Rays I→ℝ)(r): facade r (beam f r)=coeff r (paste f) := by
    rw [paste_coeff]; change _=_ • facade r (fun v=>_); rw [←map_smul];rfl
lemma beam_pulse (f: Jets.Rays I→ℝ)(h: AnalyticAt ℝ f 0)(r): Agate (beam f r):= fun v l=>Tensor.coeff_symm h.contDiffAt (dotI ∘ v) l
lemma beam_seed (f: Jets.Rays I→ℝ)(h: AnalyticAt ℝ f 0)(r): beam f r=marble r (coeff r (paste f)):= facade_unique (beam_pulse f h r) (marble_agate _ _) (by rw [beam_price, marble_grade,MvPolynomial.homogeneousComponent_eq_self (paste_grade ..)])
variable [DecidableEq I]
omit [Fintype I] in lemma coast_beam (v:chain I r):(fun i => Pi.single (v i) (1:ℝ))= dotI ∘ v:= by funext i j; by_cases h:j=v i <;> simp [dotI,h]
lemma beam_note (f:Jets.Rays I→ℝ)(r): recording (fun v=> (beam f r v:ℂ))=noteAt f r:= by
    rw [note_map, enlarge]; apply congr_arg; funext v; rw [coast_beam v];rfl
lemma grain_note (T S:Tile I r)(h: recording (fun i=>(T i:ℂ))=recording (fun i=>(S i:ℂ))): T=S := by
   funext v; let p (i:Fin r):I→ℂ:= Pi.single (v i) 1
   have he (T:Tile I r): recording (fun i=>(T i:ℂ)) p=T v:= by
       rw [recording_apply,Finset.sum_eq_single v];swap;· intro b _ hb; obtain ⟨i,hi⟩:=Function.ne_iff.mp hb; rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [p,hi] : p i (b i)=0),zero_mul]
       all_goals simp [p]
   exact Complex.ofReal_injective (by rw [← he, h,he])
lemma convert_note {f g:Jets.Rays I→ℝ}(h:AnalyticAt ℝ f 0)(hp:AnalyticAt ℝ g 0)(hh:coeff r (paste f)=coeff r (paste g)): noteAt f r=noteAt g r:= by
   rw [←beam_note,←beam_note,beam_seed f h, beam_seed g hp, hh]
end coefficients

def Matched (T: Tile (edgeL G) (t+1))(f:∀ n,Link G n→ℝ):Prop:= ∀ n,cum 0 n T=beam (f n) _
lemma matched_iff (T: Tile (edgeL G) (t+1))(f: ∀ n, Link G n→ℝ) (h: Up T)(H:Bail (fame _) σ T A)(hs:0≤ σ): Matched T f ↔ ∀ n, Recorded (pixel T) (f n) 0 := by
    constructor
    · intro a n p v i; rw [← lit_pixel T h p H hs v i, a n,beam_note]; simp
    intro ht n; apply grain_note; rw [beam_note]; apply relay_ext; intro x
    let p := Prod.fst ∘ x;let v i:= (x i).2.2; let i j:=(x j).2.1
    change recording (fun a=> (cum 0 n T a:ℂ)) (glyph p v i)=noteAt _ _ (glyph p v i); rw [lit_pixel T h p H hs, ← (show noteAt _ _ (glyph p v i)=collected (pixel T) p v i from sub_eq_zero.mp (norm_le_zero_iff.mp (ht n p v i)))]
lemma Matched.agate {T:Tile (edgeL G) (t+1)}{f:∀ n,Link G n→ℝ}(h:Up T)(H:Bail (fame _) σ T A)(hs:0≤σ)(e: Matched T f)(p:∀ n, AnalyticAt ℝ (f n) 0): Agate T:=
    light_agate (spark T 0 hs H h) (.of_forall fun n=> e n ▸ beam_pulse _ (p n) _)

-- real correction needs only sign at **finite quadrant**

def histo (L: Picture G t) (p:chain (Loc G 1) (t+1)) (x: Shift (Keys t)): ℝ:= (market (L (Prod.snd ∘ p) (Prod.fst ∘ p)) 0 x).re
def radio (L:Picture G t): Tile (edgeL G) (t+1):= fun v=> histo L (arcType v) (arcSlot v)
lemma radio_up (L:Picture G t): Up (radio L):= by intro x v; unfold radio; congr 1;ext;simp [arcSlot]
lemma radio_allele (L:Picture G t)(x): allele (radio L) x=histo L x:= by ext i; unfold allele radio; rw [pack_shift,pack_ship]
def radioCost (G: Gauge)(σ:ℝ)(t:ℕ):= ((Fintype.card (chain (Loc G 1) (t+1))):ℝ)*(2*((1+σ/4)/(σ/4)))^(Fintype.card (Keys t))
lemma radio_charges (G:Gauge)(t:ℕ)(hσ:0<σ): 0≤ radioCost G σ t:=by unfold radioCost; positivity
lemma radio_money {L:Picture G t}(h:∀ i j,Firm σ A (L i j))(hs:0<σ)(ha:0≤A): Bail (fame _) (σ/2/2) (radio L) (A*radioCost G σ t):= by
   let D:= A*(2*((1+σ/4)/(σ/4)))^(Fintype.card (Keys t));have hD:0≤D:=by unfold D; positivity
   have he (p:chain (Loc G 1) (t+1)): Width (σ/2) D (allele (radio L) p):= by
      let hh:= h (Prod.snd ∘ p) (Prod.fst ∘ p); rw [radio_allele]; exact Work.F07.widthRealPart (hh.1.issues hh.2 _ (σ/4) (by positivity) (by positivity) (by linarith))
   unfold radioCost; rw [mul_left_comm]; exact allele_bill (radio L) (radio_up L) he (by positivity) hD
lemma radio_rule {L:Picture G t}(h: ∀ i j,Firm σ A (L i j)){f:∀ n: Side,Link G n→ℝ}(hr:∀ n,Recorded L (f n) 0)(n:Side): Recorded (pixel (radio L)) (f n) 0:= by
    have hE (p: chain (Site n) (t+1))(i: Stationary.Ink G (t+1))(j): noteAt _ _ (glyph (m:=n) p i j)=collected L p i j:= sub_eq_zero.mp (norm_le_zero_iff.mp (hr n p i j))
    intro p i j; rw [show noteAt (f n) (t+1) (glyph p i j)=_ from hE p i j]; unfold collected; split;swap;· simp
    next hp =>
       have hf:L i j (outphase p)=star (L i j (-outphase p)):= by
          have hm: ∑ k, (-p) k=0:= by simp only [Pi.neg_apply,Finset.sum_neg_distrib,hp, neg_zero]
          have hx:=hE (-p) i j; rw [glyph_flips,← note_fixed, hE p i j,collected,collected,if_pos hp, if_pos hm, (reflection_negative p).apply (h i j) ((h i j).in_range (out_real (-p)))] at hx
          have hh := congr_arg star hx
          have hz:(Fintype.card (Site n):ℂ)≠0:= by exact_mod_cast (ne_of_gt (Fintype.card_pos (α:=Site n)))
          simp only [star_star,star_mul,star_natCast] at hh
          exact mul_left_cancel₀ hz (hh.trans (mul_comm ..))
       have he : pixel (radio L) i j (outphase p)=L i j (outphase p):= by
          rw [pixel,radio_allele]; change readable (fun x=> (market (L i j) 0 x).re) _=_;rw [re_cast (h i j) (out_real p),←hf];ring
       rw [he]; simp only [sub_self,norm_zero,le_refl]
-- universal inverse
lemma radio_matched {L:Picture G t}(h: ∀ i j,Firm σ A (L i j)){f:∀ n: Side,Link G n→ℝ}(hr:∀ n,Recorded L (f n) 0) (hs:0<σ)(ha:0≤A): Matched (radio L) f:= (matched_iff (radio L) f (radio_up L) (radio_money h hs ha) (by positivity)).mpr (radio_rule h hr)
end YM.FormalBulk08.Broc
