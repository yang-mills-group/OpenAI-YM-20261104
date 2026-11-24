import YM.OPE.Compatible.Broma.Oval
/-!
# Dual Tau billing at all orders. linked push
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose Votive Alps Roles
variable {n c f:Side}{I J M:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v:ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
lemma tipComp {X:Type}{p:M→ Row I J}{v u:M→ℝ}{s:ℝ}(g:X→M)(h:Tip s p v u):Tip s (p∘g) (v∘g) (u∘g):=by obtain ⟨b,h,k,H⟩:=h;exact ⟨b,h,k,fun i=>H (g i)⟩
lemma loanComp {X:Type}{p:M→ Script I d}{v u:M→ℝ}(g:X→M)(h:Loan m p v u):Loan m (p∘g) (v∘g) (u∘g):=by obtain ⟨b,h,k,H⟩:=h; exact ⟨b,h,k,fun i=> H (g i)⟩
lemma augComp {X:Type}{p q:M→ Script I d}{u v:M→ℝ}(h:Auger m p q v u)(g:X→M):Auger m (p∘g) (q∘g) (v∘g) (u∘g):= ⟨loanComp g h.A,loanComp g h.B,loanComp g h.D⟩
variable (B:Medal P G K.K P.J)(H:LocalRatio R)(hp:Crest G P K.K m)(hs:G.Simple)
local notation "X!" => TileC T P p R b
local notation "u!" => (upperX:X!→ℝ)
local notation "q!" => (downK:X!→ℝ)
local notation "PK" => (UA (H:=T) (P:=P) (p:=p) (V:=R) (C:=b))
local notation "PJ" => (VA (H:=T) (P:=P) (p:=p) (V:=R) (C:=b))
abbrev Yarn (G:Gauge)(P:Patch)(K:KernelChoices)(R:ChartRatio G)(p:PathData G)(c:Clip)(b:ℝ): Story (Flume.Script.Tile G P.L):=⟨tide3 P K p c,tide4 P K p c,tide2 P K p c R b⟩
variable {z:ℝ}
include hs H hp B
lemma worried (s:ℝ) (k:ℕ) (he:k ≤ m): ∀ j:Ask, Auger k (fun i:X! => Paloma (Yarn G P K.K R (PK i).live (PK i).clip s) j) (fun i:X! => Paloma (Yarn G P K.K R (PJ i).live (PJ i).clip s) j) q! u! :=by
      obtain ⟨d,W,hd,F,f⟩:= running T P B p R b hp; obtain ⟨hg,hb,Hx⟩:= energyProd (H:=T) (p:=p) (C:=b) H hp hs; have hy(t:ℕ)(hv:0<t)(h:t≤4): Auger k (boardA PK t) (boardA PJ t) q! u! :=by
           have ht := payTravel PK PJ (r:=t) (fun i=> ((PK i).fullK t).here _) (fun i=> ((PJ i).fullK t).here _) (m:=m) (Z:=q!) (Y:=u!) (hg t hv h); exact ⟨boardLoan PK (F.uni₁ t k) F.fuel,boardLoan PJ (F.uni₂ t k) F.fuel,ht.crush he⟩
      have hh : Auger k (fun i:X! => collarY P (UA i).live) (fun i:X! => collarY P (VA i).live) q! u!:=by
           obtain ⟨hU,hV⟩:=LeafLoan (H:=T) (P:=P) (p:=p) (V:=R) (C:=b) (m:=m) (r:=2); let f(i:X!):=(UA i).liftZ 2; have hh:= Loan.plat (drip G P.L) (drip_cash G P.L) (Hx.crush he); refine ⟨Loan.plat (drip G P.L) (drip_cash G P.L) (hU.crush he), Loan.plat (drip G P.L) (drip_cash G P.L) (hV.crush he),?_⟩; convert! hh using 1; ext1 i; exact (volVSub (drip_cash G P.L) (p:=(UA i).liftZ 2) ((UA i).fullL 2|>.here _) ((VA i).fullL 2|>.here _)).symm
      have hV:= auger_roll (plusA (plusA (auger_roll (hy 2 (by decide) (by decide)) (-s)) (auger_roll hh (-1)) F.fuel (fun i=> (F.tune i).le)) (appVan (Loan.fixed _ (Boxes.folk_cap (G:=G) P R))) F.fuel fun i=>(F.tune i).le ) ((2:ℝ)⁻¹)
      intro j; fin_cases j
      · exact auger_roll (hy 3 (by decide) (by decide)) (-6)⁻¹
      · exact auger_roll (hy 3 (by decide) (by decide)) (-6)⁻¹
      · exact auger_roll (hy 4 (by decide) le_rfl) (-24)⁻¹
      · exact ⟨hV.A.twirl.land,hV.B.twirl.land,Loan.stilt hV.A hV.B hV.D⟩
      exact nilA u! q! _ _ k
lemma dockW (s:ℝ) (k:ℕ)(he:k ≤ m) (g:M→TileC T P p R b)(X:M→Muse G) (hX:∀ i j,Loan k (fun x=>X x i j) 1 (u! ∘ g)) (q:Phase)(d r:ℕ):
     Auger k (fun i=> sculpt P K.K (Qmark B PK (g i)) (PK (g i)) R s (X i) d q r) (fun i=> sculpt P K.K (Qmark B PJ (g i)) (PJ (g i)) R s (X i) d q r) (q! ∘ g) (u! ∘g):=by -- ORDER sculpt expects Box THEN Alps
       obtain ⟨F,Ω,hF,Ht,f⟩:= running T P B p R b hp
       have hv:1 ≤ u! ∘g:=fun i=>Ht.fuel _; have ht:0 ≤ q! ∘g:=fun i=>(Ht.tune (g i)).le; have hQ (j k') : Auger k (fun i=> branchOut P G (X i) j k') (fun i=>branchOut P G (X i) j k') (q! ∘g) (u! ∘g):=by
            obtain ⟨s,a,hs,H⟩:=drip_cash G P.L; exact appVan (clay 0 (A:=fun _:M=> drip G P.L) (s:=s) (show Tip s _ _ _ from ⟨max a 0,le_max_right ..,0,fun i=>strip_mono H le_rfl (by simp only [pow_zero,mul_one,Pi.one_apply]; exact by simp)⟩) (hX j k') hv hs)
       have hb: Silk Ω (fun i=>(Qmark B PK (g i)).dot) (fun i=>(Qmark B PJ (g i)).dot) (q! ∘g) (u! ∘g):=⟨tipComp g Ht.post₁,tipComp g Ht.post₂,tipComp g Ht.dist⟩
       let V(i:X!):=Yarn G P K.K R (UA i).live (UA i).clip s;let Y(i:X!):=Yarn G P K.K R (VA i).live (VA i).clip s
       have hx:= Wealthy (P:=V∘g) (Q:=Y∘g) d r q (fun i=>augComp (worried B H hp hs s k he i) g) (areRoot (J:=Shade G) hb ht hv) hQ Ht.price hv ht
       have hh: Silk Ω (fun i=>(Qmark B PK (g i)).main) (fun i=>(Qmark B PJ (g i)).main) (q! ∘g) (u! ∘g):=⟨tipComp g Ht.ext₁,tipComp g Ht.ext₂,tipComp g Ht.dist₁⟩
       exact augBour (trope (cycleMar hh) hx (fun i=>Ht.tune _) hv Ht.price)
end YM.OPE.Drift
