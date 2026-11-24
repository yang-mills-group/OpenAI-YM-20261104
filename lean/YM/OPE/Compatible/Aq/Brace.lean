import YM.OPE.Compatible.Aq.Du
/-!
# Common powers for a sequence of patch sides

If each patch side is a power of three, `YM.OPE.Stroke.risesU` gives arbitrarily large odd sides that are powers of every side in a finite prefix.
`freedom` uses these common powers to choose a monotone sequence of sides satisfying the sheet's size conditions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
variable {H:LocalRatio R}{hs:G.Simple}
open RG.Supply
variable {d' k':ℕ→ℕ}
lemma risesU (n i:ℕ)(S:ℕ→Patch)(hs:∀ i,∃ j,(S i).L=(3:Side)^j): ∃ v:Side, n ≤ v.val∧ Odd v.val ∧∀ k ≤ i,∃ r:ℕ,v=(S k).L^r:=by
      choose k hk using hs; let z:= ∏ j∈ range (i+1),k j; have hv(j):0<k j:=Nat.pos_of_ne_zero (fun h=>by have hp:=(S j).coarse; rw [hk _, h,pow_zero] at hp; contradiction)
      have hp:0<z:= prod_pos (fun j _=>hv j); let C:Patch:=⟨3,5,by omega,by decide,⟨1,rfl⟩⟩; obtain ⟨x,hx,hh,hy⟩:= widens C n; let v:= C.L^(z*x); refine ⟨v,hx.trans ?_, ?_,fun a ha=> ?_⟩
      · rw [PNat.pow_coe,show v.val=_ from PNat.pow_coe ..]; exact pow_le_pow_right₀ (by change 1 ≤ 3; omega) (by nlinarith only [hp])
      · rw [show v.val=_ from PNat.pow_coe ..]; exact C.odd_side.pow
      obtain ⟨m,hM⟩:= dvd_prod_of_mem k (mem_range.mpr (show a < i+1 by omega)); use m*x; unfold v; change (3:Side)^_=_; rw [hk, ← pow_mul,← Nat.mul_assoc]; exact congrArg (fun i=>(3:Side)^(i*x)) hM
lemma freedom (Y:Sheet G)(h:G.Simple)(S:ℕ→Patch)(hs:∀ i,∃ j,(S i).L=(3:Side)^j): ∃ Z:Rolls Y, ∀ i,∀ j ≤ i,∃ r,(Z.L i)=(S j).L^r:=by
      choose n hn using fun i=> Rolls.eventually_large Y h i; choose V hV hp H using fun i j=>risesU (max (n i) j) i S hs; let L(i:ℕ):Side:= Nat.rec (V 0 0) (fun k r=> V (k+1) r.val) i; have hg(i):∃ j,L i=V i j:=by cases i with| zero=>exact ⟨0,rfl⟩|succ i=>exact ⟨(L i).val,rfl⟩
      have hx(i): Large Y i (L i):=by obtain ⟨a,ha⟩:=hg i; rw [ha]; exact hn i _ ((le_max_left ..).trans (hV i a)) (hp i a)
      refine ⟨⟨L,hx,monotone_nat_of_le_succ fun j=>le_trans (le_max_right ..) (hV (j+1) (L j).val)⟩,fun i j hj=>?_⟩
      obtain ⟨a,ha⟩:=hg i; change ∃ r,L i=_; rw [ha]; exact H i a j hj
variable {L:PriceBook H T} {u':M→ℝ}
lemma liberty (Y:Sheet G)(S:(i:ℕ)→Coach H L hs i (d' i) (k' i)):∃ Z:Rolls Y,∀ i,∀ j ≤ i,∃ r,Z.L i=(S j).S.L^r:= freedom Y hs (fun i=>(S i).S) fun i=>⟨(S i).J,(S i).crisp⟩
lemma receiveLab (Z:Coach H L hs e d k)(a:Axis)(hk:e+e<k)(he:Z.S.J≤j)(Y:(i:M)→ Alps K T j (u' i))(hv:1 ≤ u')(h:∀ i,(Y i).clip=p): ∃ W:Z.Z.Ω M u', Z.Z.Floss Y W (Z.S.order_cut.trans he) (le_trans zero_le_one hv) k Z.Glp a := by
   exact portraits Z.Glp Z.Z a Z.q Z.hq le_rfl Z.ho hk Z.hp Z.holds Z.receives L.h j he p u' Y hv h
end YM.OPE.Stroke
