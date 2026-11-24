import YM.Integration.WilsonNeutralPointWeakSalary
import YM.FormalBulk08.Tundra.Lamp

/-! Changed Wick terms at one selected digit. Both histories retain their own
quiet field, original forest and kinetic restamp. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPointWeakWick
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Quire Palm Grail Chapel Borough Sable Tundra Aster Series Work.F03 Work.F05 Work.F08
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical

variable {G:Gauge}{K:KernelChoices}{j t d E D e r u:ℕ}{X:Type}
variable {J U:X→ℕ}{F:∀i:X,Flight (J i) (U i)}{V:∀i:X,Lodge (F i).patch}
variable {Z L:∀i,Train (J i)}{H:∀i,(F i).patch.Branches K G}
variable {τ:Time X}{σ η δ g:X→ℝ}{a:hue G}{o:Loc G 1}
variable {W Y:X→Pot G}{T S:X→Anthem D G}

def primitive (P:Flight j t)(V:Lodge P.patch)(W:Pot G)(ρ:ChartRatio G)(H:P.patch.Branches K G)
    (T:Anthem D G)(d k:ℕ)(x:Site P.L)(hL:2≤P.L.val)(f:Studio D):Pot G:=
  (P.L.val:ℝ)^d • braise P V W (stepsong P T hL f x) ρ H k

def higher (P:Flight j t)(V:Lodge P.patch)(W:Pot G)(ρ:ChartRatio G)(H:P.patch.Branches K G)
    (T:Anthem D G)(d k e r:ℕ)(x:Site P.L)(hL:2≤P.L.val)(f:Studio D):Tile (edgeL G) r:=
  (P.L.val:ℝ)^d • plusB P V W (stepsong P T hL f x) ρ H k e r

def restoration (a:hue G)(P:Flight j t)(V:Lodge P.patch)(W:Pot G)(ρ:ChartRatio G)(H:P.patch.Branches K G)
    (T:Anthem D G)(d k e r:ℕ)(x:Site P.L)(hL:2≤P.L.val)(f:Studio D):Tile (edgeL G) r:=
  higher P V W ρ H T d k e r x hL f +
    ∑ s∈Finset.range e,bill (bookH (epoch a P V K W ρ H)) (bookU (epoch a P V K W ρ H)) e s r •
      primitive P V W ρ H T d k x hL f s r

theorem split (P:Flight j t)(V:Lodge P.patch)(W:Pot G)(ρ:ChartRatio G)(H:P.patch.Branches K G)
    (T:Anthem D G)(d k e r:ℕ)(x:Site P.L)(hL:2≤P.L.val)(f:Studio D):
    primitive P V W ρ H T d k x hL f e r =
      WilsonNeutralPointSalary.land P K V T d e r x hL f + higher P V W ρ H T d k e r x hL f:=by
  unfold primitive WilsonNeutralPointSalary.land higher
  simp only [Pi.smul_apply,braiser,smul_add]
  rfl

theorem recorded (a:hue G)(P:Flight j t)(V:Lodge P.patch)(W:Pot G)(ρ:ChartRatio G)(H:P.patch.Branches K G)
    (T:Anthem D G)(d k:ℕ)(x:Site P.L)(hL:2≤P.L.val)(e r:ℕ)(f:Studio D):
    WilsonNeutralPointMatrix.child P V W a ρ H hL d k x T f e r =
      WilsonNeutralPointSalary.land P K V T d e r x hL f + restoration a P V W ρ H T d k e r x hL f:=by
  let coin:=epoch a P V K W ρ H
  have he:bill (bookH coin) (bookU coin) e e r=1:=by
    unfold bill;rw [Nat.sub_self];exact Fresh.mul ((book_fresh coin).pow _) ((book_guard coin).pow _)
  dsimp only [coin] at he
  unfold WilsonNeutralPointMatrix.child Sierra.enterStep Wine.stamp
  simp only [Pi.smul_apply,Finset.sum_range_succ,he,one_smul,smul_add,Finset.smul_sum]
  have diag:=split P V W ρ H T d k e r x hL f
  unfold primitive at diag
  unfold restoration primitive
  simp only [Pi.smul_apply] at diag ⊢
  rw [diag]
  simp_rw [smul_comm ((P.L.val:ℝ)^d)]
  abel

private theorem select {I:X→Type}{A B:∀i,Studio D×I i→Tile (edgeL G) r}(x:∀i,I i)
    (h:Lacy u τ (fun _ _=>(0,o)) (fun _=>1) δ (fun i (p:Studio D×I i)=>g i*‖p.1‖) A B):
    Blizzard u τ o δ g (fun i p=>A i (p,x i)) (fun i p=>B i (p,x i)):=by
  rcases h with ⟨⟨a,ha,pa,ba⟩,⟨b,hb,pb,bb⟩,⟨c,hc,pc,bc⟩⟩
  exact ⟨⟨a,ha,pa,fun i p=>ba i (p,x i)⟩,⟨b,hb,pb,fun i p=>bb i (p,x i)⟩,
    ⟨c,hc,pc,fun i p=>bc i (p,x i)⟩⟩

variable {ρ:ChartRatio G}(w:Wells τ F V H ρ a σ η δ Z L W Y E)
variable (credit:Soft τ (fun i=>(η i)⁻¹))(hL:∀i,2≤(F i).L.val)(hg:∀i,0≤g i)(x:∀i,Site (F i).L)
include w credit hL hg x

theorem linear (ht:Blizzard u τ o δ g (fun i p=>T i p e r) (fun i p=>S i p e r))(d):
    Blizzard u τ o δ g (fun i p=>WilsonNeutralPointSalary.land (graded F Z i) K (V i) (T i) d e r (x i) (hL i) p)
      (fun i p=>WilsonNeutralPointSalary.land (graded F L i) K (V i) (S i) d e r (x i) (hL i) p):=by
  let A(i:X):=Studio D×Site (F i).L
  have op:=colds (f:=fun i (p:A i)=>chief (graded F Z i) (lift p.2,o) o)
    (star_w w credit (fun i=>show (1:ℝ≥0)≤1 from le_rfl)
      (fun i=>show (1:ℝ≥0)≤(F i).L.val*1 from by rw [mul_one];exact Nat.one_le_cast.mpr (F i).L.pos)
      o (landing w hL hg ht))
  simp_rw [chief_h o _] at op
  exact Matched.amp (select x op) (Pact.constant (w.air.pows d))

theorem changed (hx:e≤E)(ht:∀j m,precede e r j m → 0 < m → 
    Blizzard u τ o δ g (fun i p=>T i p j m) (fun i p=>S i p j m))(d k):
    Blizzard u τ o δ g (fun i p=>higher (graded F Z i) (V i) (W i) ρ (H i) (T i) d k e r (x i) (hL i) p)
      (fun i p=>higher (graded F L i) (V i) (Y i) ρ (H i) (S i) d k e r (x i) (hL i) p):=by
  let A(i:X):=Studio D×Site (F i).L
  have op:=plasters (U:=A) (T:=fun i z=>stepsong (graded F Z i) (T i) (hL i) z.1 z.2)
    (S:=fun i z=>stepsong (graded F L i) (S i) (hL i) z.1 z.2) w credit
    (fun i=>show (1:ℝ≥0)≤1 from le_rfl)
    (fun i=>show (1:ℝ≥0)≤(F i).L.val*1 from by rw [mul_one];exact Nat.one_le_cast.mpr (F i).L.pos)
    _ _ k o hx (fun j m prior hp=>landing w hL hg (ht j m prior hp))
  simp_rw [chief_h o _] at op
  exact Matched.amp (select x op) (Pact.constant (w.air.pows d))

theorem settled (hx:e≤E)(ht:∀j m,precede e r j m→
    Blizzard u τ o δ g (fun i p=>T i p j m) (fun i p=>S i p j m))(d k):
    Blizzard u τ o δ g (fun i p=>restoration a (graded F Z i) (V i) (W i) ρ (H i) (T i) d k e r (x i) (hL i) p)
      (fun i p=>restoration a (graded F L i) (V i) (Y i) ρ (H i) (S i) d k e r (x i) (hL i) p):=by
  have hf i:Fresh (epoch a (graded F Z i) (V i) K (W i) ρ (H i)):=
    (sig_mat a _ (ripeness (F:=F) w.pharmacy w.church w.aV i) K.penalty_pos (w.church i)).1
  have hh i:Fresh (epoch a (graded F L i) (V i) K (Y i) ρ (H i)):=
    (sig_mat a _ (ripeness (F:=F) w.pharmacy w.church w.bV i) K.penalty_pos (w.church i)).1
  obtain ⟨price,stampPrice⟩:=w.weight.goods hf hh
  unfold Blizzard restoration
  apply Matched.plus (changed w credit hL hg x hx (fun j m p _=>ht j m p) d k)
  apply matched_sums _
  intro j hj
  rw [Finset.mem_range] at hj
  apply Matched.amp _ (price.income stampPrice _ _ r (by omega))
  simp_rw [split]
  exact Matched.plus (linear w credit hL hg x (ht j r (Or.inl hj)) d)
    (changed w credit hL hg x (hj.le.trans hx) (fun i m earlier _=>ht i m (by unfold precede at *;omega)) d k)

end YM.Integration.WilsonNeutralPointWeakWick
end
