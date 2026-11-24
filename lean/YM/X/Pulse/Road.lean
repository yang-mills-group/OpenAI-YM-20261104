import YM.X.Pulse.Tunic
/-!
# reality, Unit and Signed spin of unheated stencil α families. independent of ℒ
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Pulse
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open Stems hiding X
open Crate Crate.Fund Hinge Spindle
open scoped Topology ContDiff BigOperators Classical
variable {q:ℕ+}{n:Side}{k d:ℕ}{R:ℝ}{I V T:Type*}{G:Gauge}
open Pert.Position Maxwell Maxwell.Free Bare Function Pert.RawLabels
variable {F:Labels.Frames G}(S:Bare.Shop F) (w:Floor R)
local notation "E"=> Pert.Position.E F
local notation "A"=> F.level d
local notation "L"=> Labels.Label G d
local notation "E₀"=> epsilon q k
variable (Y:T→ℕ)
section budget
variable [AddCommGroup V][Module ℂ V][AddCommGroup T][Module ℂ T]
abbrev Trust (q:ℕ+)(V:Type*)[AddCommGroup V][Module ℂ V] := Badge V (Charged q) ⊤
variable {a:ℕ→V}{c:ℕ→ℂ}
lemma stabilize (h:Charged q c)(hp:a∈Trust q V): (fun i=> c i • a i)∈Trust q V:=by
    induction hp using Submodule.span_induction with
    | mem _ p=> obtain ⟨p,v,hB,g,rfl⟩:=p; simp_rw [smul_smul]; exact badged _ (h.mul hB) g
    | zero=> simp only [Pi.zero_apply,smul_zero]; exact Submodule.zero_mem _
    | add p q _ _ x y=> simp only [Pi.add_apply,smul_add]; exact Submodule.add_mem _ x y
    | smul p y _ v=> simp only [Pi.smul_apply, smul_comm (c _) p]; exact Submodule.smul_mem _ p v
lemma bona (x:V): (fun _:ℕ=> x)∈Trust q V:=ordered le_top (fun p h=>charged h) (stead x)
lemma traverse (h:a∈Trust q V)(f:V→ₗ[ℂ] T): (fun i=> f (a i))∈Trust q T:= moved f (fun _ _=> by simp) h
lemma traverseG (h:Charged q c): Charged q (fun i=> star (c i)):= by
    obtain ⟨b,hb⟩:=h; refine ⟨b,isBigO_norm_left.mp ?_⟩; simpa [norm_star] using! hb.norm_left
lemma traverseS (h:a∈ Trust q V)(f: V→ₛₗ[starRingEnd ℂ] T): (fun i=> f (a i))∈ Trust q T:= by
    induction h using Submodule.span_induction with
    | mem _ p=> obtain ⟨c,v,hc,h,rfl⟩:=p; simp_rw [map_smulₛₗ]; exact badged _ (traverseG hc) Submodule.mem_top
    | zero=> simp only [Pi.zero_apply, map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ih g=> simp only [Pi.add_apply,map_add]; exact Submodule.add_mem _ ih g
    | smul a y _ h=>simp only [Pi.smul_apply,map_smulₛₗ];exact Submodule.smul_mem _ _ h
lemma dollars (h:c∈Trust q ℂ): Charged q c:= by
   induction h using Submodule.span_induction with
   | mem _ p=> obtain ⟨c,v,h,_,rfl⟩:=p; exact Charged.mul h (Charged.constant v)
   | zero=> exact Charged.zero
   | add a b _ _ x g=> exact x.add g
   | smul a b _ h=> exact (Charged.constant a).mul h
lemma pledged (h:a∈Trust q V)(f:ℕ→ V →ₗ[ℂ] T)(H:∀v:V,(fun k=> f k v)∈ Trust q T) :(fun i=>f i (a i))∈ Trust q T:= by
   induction h using Submodule.span_induction with
   | mem _ p=> obtain ⟨c,v,h,g,rfl⟩:=p; simp_rw [map_smul]; exact stabilize h (H _)
   | zero=>simp only [Pi.zero_apply,map_zero]; exact Submodule.zero_mem _
   | add x y _ _ ih t=>simp only [Pi.add_apply,map_add]; exact Submodule.add_mem _ ih t
   | smul a x _ ih=>simp only [Pi.smul_apply,map_smul]; exact Submodule.smul_mem _ a ih
variable [Fintype I]
lemma grade_sum (p:V)(f:ℕ→V→ₗ[ℂ] T)(B:Module.Basis I ℂ V)(h:∀i:I,(fun k=>f k (B i))∈Trust q T):(fun k=> f k p)∈Trust q T:= by
    rw [show (fun k=>f k p)=∑ i:I,B.coord i p • (fun k=> f k (B i)) from ?_]; exact Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (h _)
    ext1 k; rw [Finset.sum_apply]; simp_rw [Pi.smul_apply,← map_smul, ←map_sum]; exact congr_arg _ ((B.sum_repr p).symm)
end budget
include q
lemma stand_trust (p:E d): (fun k=>stand (F:=F) (epsilon q k) d p)∈ Trust q (E d):= by
    let H(k):= scaledPol (F.level d) fun g=>(epsilon q k:ℂ)^g.1; let f:ℕ→L:=fun k=> H k (physicalLabel F d p);
    have he: f ∈ Trust q L:= by
       apply grade_sum _ H (F.level d).basis; intro b; let t:= (F.level d).basis b; let s (k:ℕ):= epsilon q k ^ ((Bare.wt F b:ℕ):ℤ); rw [show (fun k=> H k t)=(fun k=> Complex.ofReal (s k) • t) from ?_]; exact stabilize poised (bona t); ext1 k; rw [show H k t= _ from zoomed (F:=F) (epsilon q k:ℂ) b]; simp [s,t]
    exact traverse he (enroll F d)
lemma huddle_trust (i:(F.level d).Index)(hq:1<q.val) :(fun k=> huddle (q:=q) (k:=k) S w i)∈Trust q (E d):= by
    let hi:= (F.level d).bound i; let wE(k:ℕ):=epsilon q k; let yA(k:ℕ):= Gravity.billet (q:=q) S (Bare.useWord S i) w k; -- E hides notation
    have ht:yA∈Trust q _:= by
       have hg : (fun i=> Complex.ofReal (epsilon q i) • yA i)∈Trust q _:= ordered le_top (fun c h=>charged ⟨0,fading h⟩) (tend_billet hq S (Bare.useWord S i) w);
       rw [show yA=(fun i=> Complex.ofReal (epsilon q i ^ (-(1:ℤ))) • (Complex.ofReal (epsilon q i) • yA i)) from funext (fun i=> by rw [smul_smul,zpow_neg,zpow_one,← Complex.ofReal_mul, inv_mul_cancel₀ (epsilon_pos q _).ne',Complex.ofReal_one,one_smul])]; exact stabilize poised hg
    exact stabilize poised (pledged (traverse ht (up F hi)) (fun k=> stand (wE k) d) stand_trust)
lemma robust (p:Pert.Position.E F d)(hq:1<q.val) :(fun k=> away (q:=q) (k:=k) S w d p)∈ Trust q _ := by
   apply grade_sum (physicalLabel F d p) (fun k=> advance (q:=q) (k:=k) S w d) (F.level d).basis; intro i; simp_rw [advance_eq]; apply huddle_trust S w i hq
end YM.PositionX.Pulse
