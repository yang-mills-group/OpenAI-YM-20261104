import YM.X.Bend.Snares
/-!
# cumulative functional. enforces shapeMom.World.Param. under ALL frame tangents in horizon.Euclid
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bend
open Maxwell Set Function MeasureTheory Lattice Wilson Next.Rank Labels Pert.Position
open Maxwell.Free Filter Metric Chir Sage Tri Ribbon Extra.FD Jet
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G} {d k m n:ℕ} {q:ℕ+} {V I:Type*} {r R:ℝ}
local notation "K"=>(atTop:Filter ℕ)
local notation "T"=>Fin 3
local notation "W"=>Bank F 6
local notation "G₀"=>pureBank F 6
abbrev Clique:=Tea→ℂ
def rankT (x:Clique) : ℂ:= x 0-(x 1*x 6+x 2*x 5+x 3*x 4)+2*x 1*x 2*x 3
lemma rank_zero : rankT 0=0:= by unfold rankT;simp
@[fun_prop] lemma rank_smooth : ContDiff ℝ ω rankT:= by
   unfold rankT; have H(i:Tea): ContDiff ℝ ω (fun x:Clique=> x i):= contDiff_apply ℝ _ _; fun_prop
lemma rank_entry (u: Clique) : fderiv ℝ rankT 0 u= u 0:= by
    let g(t:ℝ):Clique := t • u; have e : HasDerivAt g u 0:= by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const u
    apply (rank_smooth |>.differentiable (by simp) 0).hasFDerivAt.comp_hasDerivAt_of_eq 0 e (by simp [g])|>.unique; change HasDerivAt (rankT ∘ g) _ _;
    have hh(i:Tea): HasDerivAt (fun t=>g t i) (u i) 0:= hasDerivAt_pi.mp e i; have hu(i:Tea): g 0 i=0:= by simp [g]
    unfold rankT; apply HasDerivAt.congr_deriv (((hh 0).sub (((hh 1|>.mul (hh 6)).add (hh 2|>.mul (hh 5))).add (hh 3|>.mul (hh 4)))).add ((((hh 1).const_mul 2).mul (hh 2)).mul (hh 3))); simp [hu]
variable (hr:4096≤r)
local notation "Γ"=> Board7 F hr
local notation "B₀"=> beaconLabels F (Nat.le_refl 6)
local notation "D"=> deity F (Nat.le_refl 6)
def wants (hr:4096≤r)(p:Bank F 6):ℂ:= rankT (Board7 F hr p)
def Wanted (hr:4096≤r)(p:Word (Bank F 6)): Word ℂ:= Jet.run rankT (Board7 F hr ∘ p)
variable (B:Bare.Shop F) (hq:1<q.val)(hg:G.Simple)
lemma part_frame (a:ℝ→ Bank F 6)(b:ℕ→ Bank F 6)(h:Appears k a b): Act k (wants hr ∘ a) (Wanted hr b):= by
    refine Act.transit (show Act k (Γ ∘ a) (Γ ∘ b) from Act.all_picks fun i=> h.writes (menu F hr i)) rank_smooth.contDiffAt
lemma wants_real (p:Bank F 6)(h:House p): moral (wants hr p):= by have he(i:Tea):star (Γ p i)= Γ p i:= moral_menu hr p i h; unfold wants moral rankT; simp_rw [star_add, star_sub,star_add, star_mul,show star (2:ℂ)=2 by norm_num, he]; ring
lemma Wanted_real (a:ℕ→Bank F 6)(h:∀ i,House (a i)): moral (Wanted hr a k):= by
   let f:=delay a k; let hp:= part_frame hr f a (appears_delay a k); let t:= (starL' ℝ (A:=ℂ)).toContinuousLinearMap; have ht : t ∘ (wants hr ∘ f) = wants hr ∘ f:= funext (fun i=> wants_real _ _ (sighs (k:=k) i a h)); have he:= hp.linear (L:=t); rw [ht] at he; exact he.trans_at hp le_rfl
local notation "η"=> mainT r hr
lemma Sgoal (t:Test 3)(p:Bank F 6) : p 3 t (talent F (Nat.le_refl 6))= Splot.result F (measureS F t) p D:= by
    change _=p 3 t (Function.update (talent F (Nat.le_refl 6)) 0 _); rw [show deity F (Nat.le_refl 6)= talent F (Nat.le_refl 6) 0 from rfl, Function.update_eq_self]
include hg hq B
lemma harmless (A:Pert.Position.Buffer F 6): fderiv ℝ rankT (Γ G₀) (Γ (Tri.billM F (bufferL F A) G₀))=0:= by
    let f:=Tri.billM F (bufferL F A) G₀; rw [board_m hr B hq,rank_entry]; change f 3 η B₀=0; rw [price_eq, Sgoal]; unfold f; rw [Splot.pass_S (p:=D) F (measureS F η) hg (B.all_par (d:=6)) (lead_B ..) _ (fun i hi=> A.property.2.1 _ (by decide) _ hi)]; have he:=lumen B hq η; rw [show Splot.result _ _ _=0 from he]; simp
lemma slipped (A:Buffer F 6): HasDerivAt (fun t:ℝ=>wants hr (market F (t•A) G₀)) 0 0:= by
    let f(t:ℝ):=Γ (market F (t•A) G₀); let g:= Tri.billM F (bufferL F A) G₀; have h : HasDerivAt f (Γ g) 0 := hasDerivAt_pi.mpr (fun v=> let i:=menu F hr v; income i.f i.p G₀ A); have he := (rank_smooth|>.differentiable (by simp) (f 0)).hasFDerivAt.comp_hasDerivAt 0 h; rw [show f 0=Γ G₀ from (by unfold f;simp [market_zero]), harmless hr B hq hg A] at he; exact he
lemma G₁moment (n:ℕ→ Bank F 6)(hn:n 0=pureBank F 6): Wanted hr n 1=n 1 3 η B₀:= by
    unfold Wanted; rw [flow_tip _ _ (rank_smooth.differentiable (by simp) _),Function.comp_apply,hn, board_m hr B hq,rank_entry]; rfl
lemma G₀moment (n:ℕ→ Bank F 6)(hn:n 0=pureBank F 6):Wanted hr n 0=0:= by unfold Wanted; rw [run_zero,Function.comp_apply,hn, board_m hr B hq,rank_zero]
end YM.PositionX.Bend
