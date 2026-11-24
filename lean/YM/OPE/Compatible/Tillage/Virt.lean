import YM.OPE.Compatible.Tillage.Hood
/-! # Credit types. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Flume Flume.Script Frequency
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n c f L:Side}{P:Patch}{K:KernelChoices}{I J M:Type}{m k r d:ℕ}{σ C s u z:ℝ}{B:Sponsor G}{H:Seasons B}
namespace Alps
open Page Virgin Planned.PrimaryIntegral295.Carrier Boxes
variable {v w Z X:M→ℝ}(T:Medal P G B.K P.J)(U:∀ i:M,Alps B H P.J (v i))(V:∀ i:M,Alps B H P.J (w i))
abbrev Qturn (i:M):= (Qmark T U i).Fly (U i).live (U i).clip -- k unused
structure Roles (T:Medal P G B.K P.J)(U:∀ i:M,Alps B H P.J (v i))(V:∀ i:M,Alps B H P.J (w i))(s:ℝ) (Z X:M→ℝ) :Prop where
    fuel : 1≤X
    price : 0<s
    tune : ∀ i,0 < Z i
    uni₁ (r m:ℕ) : Loan m (fun i=>(U i).word r) 1 X
    uni₂ (r m:ℕ) : Loan m (fun i=>(V i).word r) 1 X
    post₁ : Tip s (fun i=> (Qmark T U i).dot) 1 X
    post₂ : Tip s (fun i=> (Qmark T V i).dot) 1 X
    dist : Tip s (fun i=> (Qmark T U i).dot - (Qmark T V i).dot) Z X
    ext₁ : Tip s (fun i=> (Qmark T U i).main) 1 X
    ext₂ : Tip s (fun i=> (Qmark T V i).main) 1 X
    dist₁ : Tip s (fun i=> (Qmark T U i).main- (Qmark T V i).main) Z X
variable {T U V}
lemma rosters {p q:Clip}(hX:1≤ X)(hp:∀ i,(U i).clip=p)(hp':∀ i,(V i).clip=q)(hZ:∀ i,0<Z i)(h:Tip σ (fun i=> (U i).root - (V i).root) Z X)(hσ:0 < σ):∃ s, Roles T U V s Z X:=by
    obtain ⟨s,h,t,c,g,z,u,w⟩:= tipsDelta T hσ hX (show 0 ≤ Z from fun i=> (hZ i).le) (fun i=> (U i).gear) (fun i=> (V i).gear) h
    exact ⟨s,hX,h,hZ,fun r m=> word_loan _ U hp,fun r m=> word_loan _ V hp', t,c,g,z,u,w⟩
namespace Roles
variable (B0: Roles T U V s Z X)
local notation "Z₁"=>fun i=> Boxes.dot (Qmark T U i)
local notation "Z₂"=>fun i=> Boxes.dot (Qmark T V i)
local notation "P₁"=>fun i=> ROOT (I:=Shade G) (Boxes.dot (Qmark T U i))
local notation "P₂"=>fun i=> ROOT (I:=Shade G) (Boxes.dot (Qmark T V i))
include B0
lemma earnX (m:ℕ): Loan m (Qturn T U) 1 X∧ Loan m (Qturn T V) 1 X:=by
    have hx:= tipRoot (J:= Shade G) B0.post₁ zero_le_one B0.fuel; have hy:= tipRoot (J:= Shade G) B0.post₂ zero_le_one B0.fuel
    have hb:= boardLoan U (B0.uni₁ 3 m) B0.fuel; have hg:=boardLoan V (B0.uni₂ 3 m) B0.fuel
    have h:Loan m (Qturn T U) (1*1*1) X:= trellisTurn hb hb hx B0.price zero_le_one B0.fuel; have h': Loan m (Qturn T V) (1*1*1) X:= trellisTurn hg hg hy B0.price zero_le_one B0.fuel; simp only [one_mul] at *; exact ⟨h,h'⟩
lemma priceX (hm:Loan m (fun i=>(U i).word 3 - (V i).word 3) Z X): Loan m (Qturn T U - Qturn T V) Z X:= by
    have hp:= tipRoot (J:=Shade G) B0.post₁ zero_le_one B0.fuel; have hy := tipRoot (J:=Shade G) B0.post₂ zero_le_one B0.fuel; have hv:0≤ Z:=fun i=> (B0.tune _).le
    have hq:= boardLoan U (B0.uni₁ 3 m) B0.fuel; have hk:=boardLoan V (B0.uni₂ 3 m) B0.fuel; have hh :=payTravel U V (fun i=> ((U i).fullK 3).here _) (fun i=>((V i).fullK 3).here _) hm
    have hz : Tip s (fun i=> (P₁) i-(P₂) i) Z X:=roots_tipδ (J:=Shade G) (S:= Z₁) (T:= Z₂) B0.dist hv B0.fuel
    exact loadedCot B0.price B0.fuel hv hp hy hz hq hk hq hk hh hh
lemma ear (r m:ℕ) : Loan m (fun i=> (Qmark T U i).Tell r-(Qmark T V i).Tell r) Z X:=by
    let S:=fun _:M=> expose (stationCall P B.K G r); have hC: Loan m S 1 X:= Loan.fixed _ (folkS (callCost P B.K G r) _)
    have h1:= pay_tt B0.ext₁ B0.price B0.fuel zero_le_one hC; have h2:= pay_tt B0.ext₂ B0.price B0.fuel zero_le_one hC; apply Loan.stilt h1 h2; exact pay_ttδ B0.ext₁ B0.ext₂ B0.dist₁ hC hC ((show S-S=0 from sub_self _).symm ▸ Loan.zero m r) B0.price B0.fuel B0.tune
lemma exc (hm:Loan m (fun i=>(U i).word 3-(V i).word 3) Z X):Loan m (fun i=> (Qmark T U i).Exc (U i).live (U i).clip - (Qmark T V i).Exc (V i).live (V i).clip) Z X:=by
    let Q:=(-3:ℝ); obtain ⟨h₁,h₂⟩:= B0.earnX m; have hh:= h₁.scaleL Q; have hq:= h₂.scaleL Q
    have ha: Loan m (Q • Qturn T U-Q • Qturn T V) Z X:=smul_sub Q (Qturn T U) (Qturn T V) ▸ (B0.priceX hm|>.scaleL Q)
    exact Loan.stilt (pay_tt B0.ext₁ B0.price B0.fuel zero_le_one hh) (pay_tt B0.ext₂ B0.price B0.fuel zero_le_one hq) (pay_ttδ B0.ext₁ B0.ext₂ B0.dist₁ hh hq ha B0.price B0.fuel B0.tune)
end Roles
end Alps
end YM.OPE.Votive
