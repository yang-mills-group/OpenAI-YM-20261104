import YM.OPE.Compatible.Vino.Zip
/-!
# τ Ward spaces. chosen capacities smaller weights
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l:ℕ}{K:Sponsor G}{T:Seasons K}{v b:ℝ}
section
-- variable order.B
abbrev Tower (I:Type)(d:ℕ)(τ:Phase→ℕ):=(j:Phase)→ Seat (d+j.val) (τ j) I
variable {τ:Phase→ℕ}
def spread (G:Gauge)(d:ℕ)(τ:Phase→ℕ):Tower (Shade G) d τ→ₗ[ℝ] Muse G:= LinearMap.pi fun i=> (lilies (τ i) _ _) ∘ₗ LinearMap.proj i -- implicit
lemma resin (X:Tower (Shade G) d τ)(h:∀ i:Phase,m ≤ τ i): Tide (spread G d τ X) d m ‖X‖:=by intro i; have hp:=sproutV (τ i) (d+i.val) (X i); exact ⟨hp.1,fun j=> ((Rill.soot_le_k _ _ (hp.2 j) (h i))).tips (norm_le_pi_norm X i)⟩
lemma bloomP (G:Gauge)(d:ℕ)(τ:Phase→ℕ):Injective (spread G d τ):=by intro a b h; funext i; exact lilies_inj (Shade G) _ _ (congr_fun h i)
-- Mine equality iff
local notation "Lf" => Tested.germ
section gauge
variable {E X F:Type} [Fintype I]
variable (R:Score I J)
local notation "K!" => Libra.Keys G I
lemma flu {x y:ℝ→Token} (h:Fitted x)(hp:Fitted y): (jur x-jur y)=O[Lf](gradeP 3) ↔ mine x=mine y :=by
    constructor; · intro he; exact (h.take.clash he).equality hp.take
    intro he; rw [show jur x-jur y=(jur x-(mine x).atK)-(jur y-(mine y).atK) from by rw [he];abel]; exact h.take.sub hp.take

lemma pores {p:ScriptJ (Libra.Keys G I)} (hp:p.B): R.Marbles p ↔ ∀ {x y s},R.Track x y s→mine (fun t:ℝ=> p (t⁻¹ • x t))=mine (fun t:ℝ=> p (t⁻¹ • y t)):=by
     have he {x y:ℝ→K!}{s:ℝ→Libra.Tile G J}(h:R.Track x y s):= flu (Fitted.arose _ _ (Gael.walk _ h.hX h.gx) hp) (Fitted.arose _ _ (Gael.walk _ h.hY h.gy) hp); refine ⟨fun h _ _ _ hP=> (he hP).1 (h.honors hP),fun h=>⟨hp,fun {x y s} ht=>(he ht).2 (h ht)⟩⟩
-- path linear and pulse

lemma addMar {p q:ScriptJ (Libra.Keys G I)} (hp:R.Marbles p)(hq:R.Marbles q): R.Marbles (p+q):=by
     refine ⟨ScriptJ.key hp.toll hq.toll,fun {x y s} h=>?_⟩ -- add seq ✟
     convert! (hp.honors h).add (hq.honors h) using 2; simp only [Pi.add_apply]; rw [JetS.rates_add,JetS.rates_add]; simp only [Pi.add_apply];ring

lemma prodMar {p q:ScriptJ (Libra.Keys G I)} (hp:R.Marbles p)(hq:R.Marbles q):R.Marbles (p*q):=by
      apply (pores R (ScriptJ.height hp.toll hq.toll)).mpr; intro x y s h; let X(i:ℝ):=i⁻¹ • x i; let Y(i:ℝ):=i⁻¹ • y i; change mine ((p∘X)*(q∘X))=mine ((p∘Y)*(q∘Y)); have hz:Gael X:=Gael.walk _ h.hX h.gx; have hu:Gael Y:=Gael.walk _ h.hY h.gy; rw [Fitted.slopes (p:=p∘X) (q:=q∘X) (Fitted.arose X p hz hp.toll) (Fitted.arose X q hz hq.toll),Fitted.slopes (p:=p∘Y) (q:=q∘Y) (Fitted.arose Y p hu hp.toll) (Fitted.arose Y q hu hq.toll), show mine _= _ from (show mine (p ∘ X)=mine (p∘Y) from (pores R hp.toll).1 hp h), show mine (q ∘ X)=mine (q∘Y) from (pores R hq.toll).1 hq h]

lemma staysP (u:Token):R.Marbles (fun _:K!=>u):=⟨fun _=>Bond.keep _,fun _=> by simp; exact Asymptotics.isBigO_zero ..⟩
end gauge
lemma lowerT (X:Tower (Shade G) d τ): ScriptJ.B (inkM (spread G d τ X) d (0:Site n)):= meridian _ _ 0 _ _ (resin X fun _=>Nat.zero_le _)
noncomputable def solar (G:Gauge)(d:ℕ)(τ:Phase→ℕ) : Submodule ℝ (Tower (Shade G) d τ) where
     carrier:=setOf fun p=>Rainbow (spread G d τ p)∧ Pathic d (spread G d τ p)
     zero_mem':=by rw [Set.mem_setOf_eq,map_zero]; refine ⟨fun _ _ _=>rfl,fun n p=> ?_⟩; rw [show inkM (0:Muse G) d p=(fun _=>0) from ?_]; exact staysP _ _; funext i; apply JetS.eta <;> exact flair0 ..
     add_mem':=by intro a b ⟨ha,h⟩ ⟨hp,hq⟩; rw [Set.mem_setOf_eq,map_add]; refine ⟨bright ha hp,fun n u=>?_⟩; rw [show inkM _ _ u= _ from (show inkM _ _ u= _ from funext fun i=>Ink_sum u i _ _ _ _ _ (resin a (m:=0) (fun i=>Nat.zero_le _)) (resin b (m:=0) fun i=>Nat.zero_le _))]; exact addMar (tor n) (h n u) (hq n u)
     smul_mem':=by intro c a ⟨h,ha⟩; rw [Set.mem_setOf_eq,map_smul]; refine ⟨brighter c h,fun n u=>?_⟩; rw [show inkM _ _ u= _ from funext fun i=>Ink_scale ..]; exact prodMar _ (staysP _ _) (ha n u)
end
end YM.OPE.Drift
