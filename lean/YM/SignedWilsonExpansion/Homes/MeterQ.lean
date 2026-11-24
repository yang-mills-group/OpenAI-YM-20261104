import YM.SignedWilsonExpansion.Homes.Switch
import YM.SignedWilsonExpansion.Homes.Universal

/-! Receipt quoted on a union of compact rosters after r: the mesh-then-period
comparison for the actual returned N word. Require true V branch. Local limits
at fixed regulator price and for each member of the roster--charge constants in
the estimate at r are regulator/placement independent, no `blunt gauge` assumption. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.SignedWilsonExpansion.Homes
open Function Filter Set MeasureTheory Extraction Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS PhysMS.Frame
open MergeProof.East Next.Rank Ward Next.Rank.East Pert.Scale Maxwell Extra.FD PhysicalNext.Repeat.Legato Run Lattice FullVolume Cells
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} {n:ℕ} {d:Caps n} {ι:Type*} {L:Filter ι}

structure BeamT (C:Family G) where
   k:ℕ
   V:Vane C k
namespace BeamT
variable (B:BeamT C)
def microphone (u:ℕ×ℕ) (d:ℕ) : (Bel C.book).Field d →ₗ[ℂ] C.label d :=
   if h:d≤B.k then (B.V.wheel.atCut u ⟨d,Nat.lt_succ_of_le h⟩).toLinearMap else 0
def Given (B:BeamT C)(f:Extraction.Order) (H:(Bel C.book).Hierarchy) (ρ:ℝ):Prop := B.V.checked f H B.k ∧ B.V.wheel.r=ρ

structure Associated (S:Table C.book) (B:BeamT C)(X:Panel S)(l:Ultrafilter (ℕ×ℕ)):Prop where
   limits : ∃ Y,Tendsto B.V.wheel.atCut (l:Filter _) (𝓝 Y) ∧
     ∀ (d:Fin (B.k+1)) v,X d v=S.project d (Y d v)
theorem housed (Hs:S.Hierarchy) (Hf:f.Ordered C S) (H:(Bel C.book).Hierarchy) (P:C.Makes)
   (U:Ultrafilter (ℕ×ℕ))(hU:(U:Filter _) ≤ f.fuse) {ρ:ℝ} (b:B.Given f H ρ) :
   ∃ X:Panel S,Associated S B X U ∧ HouseT Hs H ρ B.k X:=by
   obtain ⟨Y,hY,X,hX,p⟩:=fan Hs Hf H P B.V b.1 U hU
   exact ⟨X,⟨Y,hY,hX⟩,b.2 ▸ p⟩
end BeamT

open BeamT Wilson Extra.WeakScaling

def MICRO (C:Family G)(u:ℕ×ℕ) (f:ℕ) (x:Fin n→ Cover) (d:Caps n) (B:Fin n→BeamT C) (ρ:ℝ)(r: Fin n→ℝ)(v:MaxwellSlots C d) :=
   C.ensemble d (fun j=> location C.S f u.1 u.2 (x j)) (fun i=> BeamT.microphone (B i) u (d i) (gear C.labels (d i) (ρ/r i) (v i)))

section limits
lemma tie_bill (R:Run G)(h:G.Simple){S:Table R.family.book} {n k:ℕ} (Hs:S.Hierarchy)(hp:f.PointLimits R.family S)(x:Fin n→ Cover)(hx:Order.grid R.family k x∈conf n) (d:Caps n) (v:R.family.book.Vector d):
    Tendsto (fun i:ℕ×ℕ => R.family.ensemble d (fun j=> location R.family.S k i.1 i.2 (x j)) v) f.fuse (𝓝 (S.value d (Order.grid R.family k x) v)) := by
   let V:Fin n→ R.family.book.Token:=fun i=>⟨d i,v i⟩
   let C:=R.family
   apply Metric.tendsto_nhds.mpr; intro ε ep
   filter_upwards [bright R h Hs.smooth hp V {Order.grid C k x} isCompact_singleton (singleton_subset_iff.mpr hx) ε ep,(cofin_fst f).eventually (eventually_ge_atTop k)] with q H (hq:k≤q.1)
   let y:= fun i=> (C.S.toDepth hq q.2).count.val • x i
   have ht: Extraction.tag (C.S.a q.1) y = Order.grid C k x := by
      apply PiLp.ext; intro i; apply PiLp.ext; intro a
      change C.S.a q.1 * (((C.S.toDepth hq q.2).count.val • x i) a : ℤ)= C.S.a k * (x i a :ℤ)
      rw [show ((((C.S.toDepth hq q.2).count.val • x i) : Cover) a : ℤ) =
        ((C.S.toDepth hq q.2).count.val : ℤ) * x i a by simp]
      rw [Int.cast_mul,Int.cast_natCast, ← mul_assoc,C.S.embeds_scale]
   have H':=H y ht; change dist (lifted C q.1 q.2 V _) (S.read (Extraction.tag _ _) V) < _ at H'; rw [ht] at H';
   change dist (C.ensemble _ (fun j=> location C.S k q.1 q.2 (x j)) v) _ < _
   simp_rw [location,dif_pos hq, Ratio.embed_wrap]
   exact H'

lemma considered (R:Run G)(h:G.Simple){S:Table R.family.book}{n k:ℕ}{X:Fin n→Panel S}{r:Fin n→ℝ}{B:Fin n→BeamT R.family} (Hs:S.Hierarchy)(hp:f.PointLimits R.family S)(ρ:ℝ)(w:Points n) (x:Fin n→ Cover)(P:ρ • w=Order.grid R.family k x)(hx:ρ • w∈conf n) (d:Caps n) (hd:∀ i,d i ≤ (B i).k) (v:MaxwellSlots R.family d)
     (l:Ultrafilter (ℕ×ℕ))(hl:(l:Filter _)≤ f.fuse) (a:∀ i, Associated S (B i) (X i) l) :
    Tendsto (fun i=> MICRO R.family i k x d B ρ r v) (l:Filter _) (𝓝 (shelter (d:=d) ρ r X v w)) := by
   choose Y hY A using fun i=> (a i).limits
   let g(i):= gear R.family.labels (d i) (ρ/r i) (v i)
   let D(i):Fin ((B i).k+1):=⟨d i,Nat.lt_succ_of_le (hd i) ⟩
   let z(i):=(Y i (D i) (g i))
   have H(i) : Tendsto (fun u:ℕ×ℕ=> (B i).microphone u (d i) (g i)) (l:Filter _) (𝓝 (z i)):=by
     simp_rw [microphone,dif_pos (hd i)]
     exact Dash.arcing (tendsto_pi_nhds.mp (hY i) (D i)) tendsto_const_nhds
   rw [show shelter ρ r X v w= S.value d (Order.grid R.family k x) z from ?_]
   exact Next.UVStress.tendsto_multi _ _ _ (fun v=> (tie_bill R h Hs hp x (P ▸ hx) d v).mono_left hl) _ _ H
   unfold shelter; rw [P]
   change S.classMoment S d _ (fun i=>X i (d i) (g i))= _
   rw [show (fun i=>X i (d i) (g i)) = fun i=> S.project (d i) (z i) from funext fun i=> A i (D i) _]
   exact S.at_project S Hs.laws.toSymmetric (fun _ => le_rfl) (P ▸ hx) (fun i=> ⟨d i, z i⟩)
end limits
end YM.SignedWilsonExpansion.Homes
