import YM.RegulatorIR.Gain.Rig

/-! Evaluation rays of grain Grip. Finite-support inputs. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Gain
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Halo Halo.Sight
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{I J X Y Z:Type}{f c:Side}{P l u:ℝ}{m b t:ℕ}

def circ (Γ:Curve I J)(x:J→ℝ)(i:I):ℝ⟦X⟧:= PowerSeries.mk (fun u=> strum (Γ i u) x)
lemma tint0 (F:Layer I J)(i:I) (u:J→ℝ) : strum (fun x:Tuple J 1=> F i (x 0)) u= scanL F u i:=by
 unfold strum scanL; rw [← (Equiv.funUnique (Fin 1) J).symm.tsum_eq]; apply tsum_congr; intro b;change F i b*_=_; simp [noodle,Equiv.funUnique]
-- Finite orbit rays.

variable {A: Deck P (Foot G) (Book G f)} {B: Deck P (Foot G) (Book G c)}
variable (D:GridStep A B)(J₀:Layer (Foot G) (Foot G))(V:Bride G)
local notation "R" => grain D J₀ V

def atB (D:Deck P (Foot G) (Book G f))(B:Deck P (Foot G) (Book G c))(J₀: Layer (Foot G) (Foot G))(x:Book G c→ℝ) : Horizon G f:= (paper G f).symm (scanL (wrapL D B J₀) x)
def atP (B:Deck P (Foot G) (Book G c))(V:Bride G)(x:Book G c→ℝ)(i: Site f) : G.Color:= WithLp.toLp 2 (fun j=>scanL (scene V B (f:=f)) x (i,j))
lemma pair_even (H:Rune B f V)(x):EvenSite (atP (f:=f) B V x):=by
 intro i; unfold atP;apply congr_arg; ext j; unfold scanL; rw [moonlit H]
lemma port (h:Passport A B D J₀ V) (v:Book G c→ℝ) : circ (R).tunnel v= vow (peel (fun _=> atB A B J₀ v)) :=by
 let P:=wrapL A B J₀; ext1 i;let z:=scanL P v
 have hi: vow (peel (fun _=>atB A B J₀ v)) i= PowerSeries.C (z i) :=by
   -- explicit default? below
   unfold vow; rw [tale_const];rfl
 unfold circ; rw [hi];ext k; rw [PowerSeries.coeff_mk]; unfold Strip.tunnel Step.inert Strip.perimeter;dsimp only [grain]
 rw [leg_v D h];
 by_cases hk:k=0
 · subst k; rw [coeff_zero_C]; simp_rw [if_true]; exact tint0 P i v
 simp_rw [if_neg hk,PowerSeries.coeff_C, if_neg hk]; exact strum_zero ..
lemma lift_eq (v:Book G c→ℝ): circ (R).run v=vow (peel (current (atB A B J₀ v) (atP B V v))):=by
 ext1 x; ext1 j;rw [circ,coeff_mk];let P:=tubeO (wrapL A B J₀) (scene V B) x.1
 let u:=violetO (atB A B J₀ v) (atP B V v) x.1
 change strum (loom (pet G _ _) _) _=coeff j (routeS _ _ u)
 rw [song_jet,frame_loom];
 have ht: (fun i=>∑ b,P i b*v b)= lineTrip G u:=by
   ext1 i; rcases i with ⟨i,a⟩; fin_cases i <;> (change _ = (∑' b:Book G c,_); rw [tsum_fintype];rfl)
 rw [show (fun i=>∑ b,P i b*v b)= _ from ht]; exact pet_eval ..

-- Cover pair rays
variable [Fintype X]
variable (C:X↪ Foot G)(x:X→ℝ)

def basicB (J₀: Layer (Foot G) (Foot G))(v:Foot G→ℝ): BEdge G := timber G (scanL J₀ v)
def basicP (V:Bride G)(v:Foot G→ℝ) (x:Cover): G.Color := WithLp.toLp 2 (fun i=> scanL V v (x,i))
omit [Fintype X] in
lemma setup (v:Foot G→ℝ) : circ (R).straight v= vow (fun _=> hue (basicB J₀ v)):=by
 ext1 i;change circ _ v i=tale (fun _=> _); rw [tale_const]; ext1 k; rw [circ, PowerSeries.coeff_mk]; unfold Strip.straight Step.inert; by_cases hk:k=0
 · subst k; rw [coeff_zero_C]; simp_rw [if_true]; exact tint0 ..
 simp_rw [if_neg hk,PowerSeries.coeff_C, if_neg hk]; exact strum_zero ..
lemma stylist : circ (R).space (dilute C x) = vow (shadowU (basicB J₀ (dilute C x)) (basicP V (dilute C x))):=by
 let w:=dilute C x; ext1 i; let A:=basicB J₀ w;let u:= basicP V w; let z:= violet A u i.1; ext1 k; rw [circ, PowerSeries.coeff_mk]
 change strum (loom (pet G i.2 k) (tubeL J₀ V i.1)) _= coeff k (routeS G i.2 z)
 rw [shoots,song_jet, show scanL _ _= _ from ?_]; exact pet_eval G i.2 k z
 ext1 i; rcases i with ⟨v,b⟩;fin_cases v <;> rfl

-- caps in cover. $V$ price broad. only need finite tuple tests to detect. 
private lemma scout {U: Layer (J×G.ColorIndex) (Foot G)}(h:Billed U) : boundedC (G:=G) (fun v:J=> WithLp.toLp 2 (fun i:G.ColorIndex=> scanL U (dilute C x) (v,i))) := by
 obtain ⟨c,hc,h⟩:=h; let D := fun v:J=>WithLp.toLp 2 (fun i:G.ColorIndex=>scanL U (dilute C x) (v,i));
 have hp v i : ‖U v i‖≤ c.toReal:=by apply (ENNReal.ofReal_le_iff_le_toReal hc).mp;rw [ofReal_norm]; have hb:= (term_le (U v) 1 i).trans (h v); simpa only [Pi.one_apply,mul_one] using hb
 let b:=∑ i,c.toReal*‖x i‖
 have hb:0≤b:=Finset.sum_nonneg fun i _=>by positivity
 have hh v i: ‖D v i‖≤b:= by unfold D;rw [WithLp.ofLp_toLp, ← gated]; exact (norm_sum_le ..).trans (Finset.sum_le_sum (fun _ _=>by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hp ..) (norm_nonneg _)))
 let c:= (Fintype.card G.ColorIndex : ℝ)
 refine ⟨Real.sqrt (c*b^2),Real.sqrt_nonneg _,fun v=> ?_⟩
 apply Real.le_sqrt_of_sq_le; change ‖D v‖^2≤ _; rw [EuclideanSpace.norm_sq_eq]
 apply le_trans (Finset.sum_le_sum (g:=fun _=> b^2) (fun i _=> pow_le_pow_left₀ (norm_nonneg _) (hh v i) _)) (le_of_eq (by simp [c]))
lemma basic_cov (h:Billed J₀): boundedC (basicB J₀ (dilute C x)):= scout C x h
lemma basic_cost (h:Billed V): boundedC (basicP V (dilute C x)):= scout C x h
end YM.RegulatorIR.Gain
