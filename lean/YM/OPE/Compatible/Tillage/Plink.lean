import YM.OPE.Compatible.Tillage.Virt
/-! # Cost sensitive log pressure relation -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Flume Flume.Script Frequency
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n c f L:Side}{P:Patch}{K:KernelChoices}{I J M:Type}{m k r d:ℕ}{σ C s u z:ℝ}{B:Sponsor G} {H:Seasons B}
namespace Alps
open Page Virgin Planned.PrimaryIntegral295.Carrier Boxes
variable {v w Z X:M→ℝ}{T:Medal P G B.K P.J} {U:∀ i:M,Alps B H P.J (v i)} {V:∀ i:M,Alps B H P.J (w i)}
namespace Roles
variable (B0: Roles T U V s Z X)
section norm
variable {p q:M→Script I r} {A C: M→Script I r}
lemma sched (h:Loan m (p-q) Z X)(hp:Loan m (A-C) Z X)(hx:0 ≤ Z)(hg:1≤X): Loan m ((p+A)-(q+C)) Z X:=by rw [show p+A-(q+C)=(p-q)+(A-C) by abel]; exact h.seize hp hg hx
lemma valu (h:Loan m (p-q) Z X)(a:ℝ):Loan m ((a • p)-(a • q)) Z X:=by rw [← smul_sub]; exact h.scaleL a
end norm
include B0
lemma stockL (m:ℕ): Loan m (fun i=>(Qmark T U i).lip (U i).live (U i).clip) 1 X ∧ Loan m (fun i=>(Qmark T V i).lip (V i).live (V i).clip) 1 X:=by
    obtain ⟨h₁,h₂⟩:=B0.earnX m
    let r:=Equiv.swap (1:Fin 4) 2; have he(M':M→ Row (Tile G P.L) (Tile G P.L))(P' Q:M→Script (Tile G P.L) 4)(h:Tip s M' 1 X)(hx:Loan m P' 1 X)(hp:Loan m Q 1 X):Loan m (fun i=> (1/2:ℝ) • (((-1:ℝ) • Script.pad (M' i) (P' i) + Script.pad (M' i) (Q i))+(-1:ℝ) • Script.pad (M' i) (swing r (P' i)))) 1 X:=by
        have h1:= fuse_self B0.price B0.fuel (u:=1) zero_le_one h hx
        have h2:= fuse_self B0.price B0.fuel (u:=1) zero_le_one h hp
        have h3:= fuse_self B0.price B0.fuel (u:=1) zero_le_one h (Loan.decoys r hx)
        rw [one_mul] at h1 h2 h3; exact (((h1.scaleL (-1:ℝ)).seize h2 B0.fuel zero_le_one|>.seize (h3.scaleL (-1:ℝ)) B0.fuel zero_le_one).scaleL (1/2:ℝ))
    exact ⟨he _ _ _ (tipRoot (J:=Shade G) B0.post₁ zero_le_one B0.fuel) h₁ (boardLoan U (B0.uni₁ 4 m) B0.fuel),he _ _ _ (tipRoot (J:=Shade G) B0.post₂ zero_le_one B0.fuel) h₂ (boardLoan V (B0.uni₂ 4 m) B0.fuel) ⟩
lemma lipson (h:Loan m (fun i=>(U i).word 3-(V i).word 3) Z X)(hx:Loan m (fun i=>(U i).word 4-(V i).word 4) Z X):Loan m (fun i=>(Qmark T U i).lip (U i).live (U i).clip-(Qmark T V i).lip (V i).live (V i).clip) Z X :=by
    have ha:=B0.priceX h; obtain ⟨hf,hg⟩:=B0.earnX m
    let Q:= Qturn T U; let R:=Qturn T V; let F(i:M):= ROOT (I:=Shade G) ((Qmark T U i).dot); let G'(i:M):= ROOT (I:=Shade G) ((Qmark T V i).dot); have hp : Tip s F 1 X:=tipRoot B0.post₁ zero_le_one B0.fuel; have hp' : Tip s G' 1 X:=tipRoot B0.post₂ zero_le_one B0.fuel; have hu : 0 ≤ Z:=fun i=>(B0.tune i).le; have hv: Tip s (F-G') Z X:= roots_tipδ (J:=Shade G) (S:=fun i=>(Qmark T U i).dot) (T:=fun i=>(Qmark T V i).dot) B0.dist hu B0.fuel
    let E : Equiv.Perm (Fin 4):= Equiv.swap 1 2; let f(i:M):= swing E (Q i); let g(i:M):= swing E (R i); have hD: Loan m (f-g) Z X:= Loan.decoys E ha
    have h1: Loan m ((fun i=> Script.pad (F i) (Q i))-(fun i=> Script.pad (G' i) (R i))) Z X:= fuse_d B0.price B0.fuel hu hp hp' hf hg hv ha
    have h3: Loan m ((fun i=> Script.pad (F i) (f i))-(fun i=> Script.pad (G' i) (g i))) Z X:= fuse_d B0.price B0.fuel hu hp hp' (Loan.decoys E hf) (Loan.decoys E hg) hv hD
    have h2:Loan m ((fun i=> Script.pad (F i) (boardA U 4 i))-(fun i=> Script.pad (G' i) (boardA V 4 i))) Z X:= fuse_d B0.price B0.fuel hu hp hp' (boardLoan U (B0.uni₁ 4 m) B0.fuel) (boardLoan V (B0.uni₂ 4 m) B0.fuel) hv (payTravel U V (fun i=>((U i).fullK 4).here _) (fun i=>((V i).fullK 4).here _) hx)
    exact valu (sched (sched (valu h1 (-1)) h2 hu B0.fuel) (valu h3 (-1)) hu B0.fuel) (1/2)
lemma HortPay (V':ChartRatio G)(h:Loan m (fun i=>(U i).word 3-(V i).word 3) Z X)(hx:Loan m (fun i=>(U i).word 4-(V i).word 4) Z X): Loan m (fun i=> (Qmark T U i).Hort (U i).live (U i).clip V' - (Qmark T V i).Hort (V i).live (V i).clip V') Z X:=by
    let S(i:M):=(-1:ℝ) • Script.collarH P V'; let A i:= (Qmark T U i).lip (U i).live (U i).clip; let C i:= (Qmark T V i).lip (V i).live (V i).clip
    have hs:Loan m S 1 X:=(Loan.fixed (Script.collarH P V') (folk_cap P V')).scaleL (-1:ℝ); obtain ⟨ha,hQ⟩:= B0.stockL m; have hv: Loan m (A+S) 1 X:=ha.seize hs B0.fuel zero_le_one; have ht :Loan m (C+S) 1 X:= hQ.seize hs B0.fuel zero_le_one; have hd: Loan m ((A+S)-(C+S)) Z X:=by rw [show A+S-(C+S)= A-C by abel]; exact B0.lipson h hx
    exact Loan.stilt (pay_tt B0.ext₁ B0.price B0.fuel zero_le_one hv) (pay_tt B0.ext₂ B0.price B0.fuel zero_le_one ht) (pay_ttδ B0.ext₁ B0.ext₂ B0.dist₁ hv ht hd B0.price B0.fuel B0.tune)
end Roles
end Alps
end YM.OPE.Votive
