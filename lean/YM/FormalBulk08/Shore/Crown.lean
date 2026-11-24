import YM.FormalBulk08.Shore.Tints

/-! Gauge pull tiles are presentations of the same local unit; the rescaling
by number of tiles disappears in formal identities about the log. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Shore
open Lava Gorge Lattice Laurent Bloch Filter Set Function Reef Wilson Stationary
open Wick Lotus Orb Series PowerSeries Jets
open scoped BigOperators Classical ENNReal Topology ContDiff Matrix.Norms.Frobenius
variable {I J : Type} [Fintype I] {G : Gauge} {r : ℕ} (m n : Side)

lemma blowing (b : Jets.Rays I→Jets.Rays (wire G n)) (p : Pap (wire G (m*n))):
    roam ℝ (motor b) (shrink (n:=n) p)= roam ℝ (motor (fun z=> b z ∘ tray m n)) p := by
   unfold shrink roam; rw [change_after]; rw [show (insertAt ℝ _).comp _ = insertAt ℝ _ from ?_]
   ext <;> simp; rfl

def slope (x : Site n) := wrap (m*n) (lift x)
lemma pierces (x : Site n) : (endo m n).residue (slope m n x)=x:= by rw [slope,Ratio.residue_wrap (endo m n)]; exact wrap_lift _
lemma signed_res (s : Signed) (x : Site (m*n)): (endo m n).residue (s.act x) = s.act ((endo m n).residue x) := by nth_rw 1 2 [←wrap_lift x];rw [wrap_signed,Ratio.residue_wrap,Ratio.residue_wrap,wrap_signed]

def boiling (U : Config G n) : Config G (m*n):= fun x=> U ((endo m n).residue x.1,x.2)
lemma steep (x : Jets.Rays (wire G n)) : boiling m n (input G n x)= input G (m*n) (x ∘ tray m n) := by
   funext i; unfold boiling input; simp_rw [Work.F03.represent_link]; congr
lemma towers (i:Axis) : (endo m n).residue (step i)=step i := by rw [← wrap_step (m*n),Ratio.residue_wrap];exact wrap_step _ _
lemma tilted_boil (s : Signed) (y : Site n) (U : Config G n): boiling m n (pull s y U) = pull s (slope m n y) (boiling m n U) := by
   funext i; simp only [pull,boiling,affine]; -- Step.read
   unfold Step.read; generalize ((posDir i.2).rotate s)=d; cases d with | mk j z=> cases z <;> simp [Step.used,boiling,pierces,signed_res,towers] <;> rfl -- residue step increment
lemma reborn (w : Site n→G.El) (U : Config G n) : boiling m n (Lattice.gauge w U) = Lattice.gauge (w ∘ (endo m n).residue) (boiling m n U) := by
   funext i; simp [Lattice.gauge,boiling,towers]; rfl

variable (p : (n : Side)→ Pap (wire G n))
lemma maritime (x : Site n) (s : Signed)
   (a b : Jets.Rays I→ Jets.Rays (wire G n)) (k : Jets.Rays I→ Site n→G.El) (A : a 0=0) (B : b 0=0) (ha : ContDiffAt ℝ ω a 0) (hb : ContDiffAt ℝ ω b 0) (hk : Army k 0) (H : ∃ g:G.El,k 0=fun _=>g)
   (he : ∀ᶠ z in 𝓝 0,input G n (b z)=Lattice.gauge (k z) (pull s x (input G n (a z))))
   (hc : Civic (p (m*n))) : roam ℝ (motor a) (shrink (n:=n) (p (m*n)))=roam ℝ (motor b) (shrink (n:=n) (p (m*n))) := by
   rw [blowing,blowing];
   apply hc s (slope m n x) I _ _ (fun i=> k i ∘ (endo m n).residue) (by rw [A];rfl) (by rw [B];rfl) (contDiffAt_pi.mpr fun i=>contDiffAt_pi.mp ha (tray m n i)) (contDiffAt_pi.mpr fun i=>contDiffAt_pi.mp hb (tray m n i)) (fun i=>hk ((endo m n).residue i))
   · obtain ⟨g,h⟩:=H; use g; rw [h]; rfl
   filter_upwards [he] with z hz; change input _ _ (b z ∘ tray m n) = _; rw [←steep,hz,reborn,tilted_boil,steep]; rfl

lemma civic_shore (f : Pap (wire G n)) (T : OrbitV (Biglot (Loc G 1))) (K : ℕ→ℕ)
   (H : ∀ e r,0<r→ ∃ η : ℝ,0<η ∧ Kith η (T e r) (fun b=>rancho (p b) e r))
   (R : ∀ e r (i:Fin r), rancho f e r=cum i n (T e r))
   (hp : ∀ᶠ m in atTop, Civic (p m)) (h : ∀ e,∀ᶠ m in atTop, ∀ r,K e<r→ rancho (p m) e r=0) : Civic f:=by
   intro s x I i a b k A B ha hb hk he hv
   apply robust (fun m:Side=>shrink (n:=n) (p (m*n))) f (fun m=> (Fintype.card (Site m):ℝ)⁻¹) K (motor a) (motor b)
   · intro j; filter_upwards [(onward n).eventually (h j)] with m hm t ht
     rw [shrink,coeff_map]; change marble t (MvPolynomial.rename (tray m n) _)=0; rw [pebble,show marble t _= _ from hm t ht]; funext; simp [cores]
   · intro j r hr v; obtain ⟨η,hη,hh⟩:=H j r hr
     exact copying n p f v j (T j r) hη hh ⟨0,hr⟩ (hp.mono fun m hm=>civic_up m _ hm j r) (R j r ⟨0,hr⟩)
   exact ((onward n).eventually hp).mono fun m hm=> maritime m n p x s a b k A B ha hb hk he hv hm
end YM.FormalBulk08.Shore
