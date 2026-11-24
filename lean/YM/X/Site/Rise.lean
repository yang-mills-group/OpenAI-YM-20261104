import YM.X.Site.Ocean
/-!
# Exterior direction examples. Include arbitrary finite spans.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Ocean
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric Asymptotics
open Reed Stems Hinge Braid Fielding Print
open scoped Topology BigOperators Classical
variable {q : ℕ+} (hq:1<q.val) {n:Side} {k m v:ℕ} {G:Gauge}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "H"=> Hair G
local notation "ε"=>epsilon q
variable {R:ℝ}{p:Fielding.Walk}{A B: ℕ→ Brush G} {x:E4}
def tack (k:ℕ)(e:ℝ)(n:Side)(x:Cover)(f:Fan G):= (e^(k+1))⁻¹ • leadsL x f
def fromP (q:ℕ+)(k:ℕ)(p:Fielding.Walk)(f:Fan G):= fun i=> paints (side q i) (tack k (epsilon q i) (side q i) (p i) f)
lemma from_license (f g:Fan G)(z:Cover)(v:ℕ): flatL (fromP q k p f v) (leadsL z g)=(epsilon q v^(k+1))⁻¹ *spend (side q v) (p v) z f g:= by rw [fromP,tack,map_smul, ←taste_eval,map_smul,taste_eval,spent]; rfl
include hq
lemma different {x y:E4}{f g:Fielding.Walk}(hf:plot q f x)(hg:plot q g y)(he:x≠y): ∀ᶠ i:ℕ in Fℕ, wrap (side q i) (f i)≠wrap _ (g i):= by
    filter_upwards [plot_lift hq hf,plot_lift hq hg,(Tendsto.sub hf hg).eventually_ne (sub_ne_zero.mpr he)] with i hi h' hd; let u:= spot (ε i); change u (f i)- u (g i) ≠ 0 at hd; intro h; exact hd (sub_eq_zero.mpr (congr_arg u (hi.symm.trans ((congr_arg Lattice.lift h).trans h'))))
omit hq in
lemma named {x y:Cover} (t:Hair G)(he:wrap n x≠wrap _ (y+t.1.1)) (i:Axis)(k:G.ColorIndex): place (0:Site n) (pointB y t)≠place 0 ((x,i),k):= by
    intro h; apply he; have hh:=congr_arg (fun r:Jam n G=>r.1.1) h; change wrap n (y+t.1.1)+0=wrap n x+0 at hh; exact (add_right_cancel hh).symm
lemma contra (f:Fan G)(y:Hair G)(h:plot q p x)(hx:x≠0): ∀ᶠ i:ℕ in Fℕ, flatL (twin (side q i) y) (leadsL (p i) f)=0:= by
    induction f using Finsupp.induction_linear with
    | zero => exact Eventually.of_forall (fun i=>by simp)
    | add a b ma mb=>filter_upwards [ma,mb] with i hi hp; rw [map_add,map_add,hi,hp,add_zero]
    | single k c=>
        let w:= p+(fun _:ℕ=> k.1.1); have he: plot q w x:= by rw [← add_zero x]; exact h.add (plot.constant hq k.1.1)
        filter_upwards [different hq (plot.constant hq y.1.1) he hx.symm] with i hi; rw [leads_single,flatL,Finsupp.linearCombination_single]; change c • (if place (0:Site (side q i)) _=place 0 _ then 1 else (0:ℝ))=0; rw [if_neg (named k (x:=y.1.1) (y:=p i) hi y.1.2 y.2),smul_zero]
lemma from_afford (f:Fan G)(hx:f∈Horizontal G)(h:plot q p x)(hp:x≠0): ClearK (fromP q k p f):= by
    intro j z; let w(t:G.ColorIndex):Hair G:= ((z,j),t); filter_upwards [eventually_all.mpr fun t:G.ColorIndex=> contra hq f (w t) h hp] with i hi; apply PiLp.ext; intro t;
    change orderK j (paints _ _) z t= (0:ℝ); rw [tack,map_smul, map_smul,Pi.smul_apply]; change (ε i^(k+1))⁻¹ * _=0; exact mul_eq_zero_of_right _ ((horizontal_pays (side q i) (leadsL (p i) f) (w t) (horizontal_lead (p i) f hx)).trans (hi t))
lemma from_tide (hr:R≥0)(hx:R<‖x‖)(h:plot q p x)(f:Fan G)(hf:f∈Reed.grads G k)(hp:f∈Horizontal G): Tide q R (fromP q k p f):= by
    refine ⟨from_afford hq f hp h (by intro hi; simp [hi] at hx; linarith),fun l g hg=> ?_,fun l g hg y hy z hz=>?_⟩
    · obtain ⟨a,ha,he⟩:= gate_far hq R hr hx h; obtain ⟨c,hc,hp'⟩:= Print.cost hq (enrolled₂ g f hg hf); let b:=2+(l+k); refine ⟨c/a^b,by positivity,?_⟩; filter_upwards [he,hp'] with i hi hh z hz; let r:= epsilon q i; let n:=side q i; let s:=Print.scale n z (p i); have hs:s>0:= zero_lt_one.trans_le (Print.scale_pos ..); have hr':0<r:= epsilon_pos q i
      have hw := hi z hz; have h': a/s ≤ r:= (div_le_iff₀ hs).mpr hw; set P:= spend n z (p i) g f; have heq: (‖P‖*(a/s)^0) ≤ c/a^b*r^b:= by
          rw [pow_zero,mul_one]; refine le_trans ?_ (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h' b) (div_nonneg hc (by positivity)))
          rw [div_pow]; field_simp; apply hh z (p i) -- field
      rw [from_license,symmetry,norm_mul,Real.norm_of_nonneg (show 0≤(ε i^(k+1))⁻¹ from by unfold epsilon; positivity),Real.norm_of_nonneg (show 0≤ ε i ^(l+1) from pow_nonneg hr'.le _),pow_zero,mul_one]; rw [pow_zero,mul_one] at heq;
      rw [inv_mul_eq_div,div_le_iff₀ (pow_pos hr' _), mul_assoc,← pow_add]; exact (show l+1+(k+1)=b from by omega) ▸ heq -- orientation
    simp_rw [from_license]
    let B(n:Side)(x y:Cover) := spend n x y f g; let F(i:ℕ):= B (side q i) (p i) (z i); let b:=2+(k+l)
    have ht(i:ℕ): ((ε i^(l+1))⁻¹)*((ε i^(k+1))⁻¹ * F i) = F i/(ε i)^b:= by rw [←mul_assoc,← mul_inv,←pow_add,show l+1+(k+1)=b from by omega,mul_comm]; rfl
    simp_rw [show ∀ i:ℕ,(spend (side q i) (p i) (z i) f g)= F i from fun _=>rfl,ht]; exact Print.glides hq (enrolled₂ f g hf hg) (ne_of_apply_ne (‖·‖) (ne_of_gt (hy.trans_lt hx))) h hz
end YM.PositionX.Ocean
