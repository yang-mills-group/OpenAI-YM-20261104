import YM.RG05Readout.Chalice.PhaseA
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Chalice
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Petals Petals.Kernel Bay Dash
/-! Pass regulators. Manifest erasures with every stencil estimate
 first keep the exact witnesses, can sum in actual volume. Then FD weak
 limit at all orders needed for the reading, no collision costs. -/
variable {v:ℕ}
local notation "V"=> Fin v
local notation "U"=> Fin n
local notation "Z"=> C.side N p
variable (F':Test (v+n))(s:Fin v→ℕ)(F:(i:Fin v)→Leafage C (s i))
variable {R₀: Fin n→C.book.Token} {A T:YM.Table C.book}{L0:ℕ→YM.Table C.book}{R:Dash.Bin A}{E:DiffPlan T}(H: Next.Extract.Base C f A L0 R T E)
local notation "g!"=> Fin.append s (fun i=> (R₀ i).1)
local notation "Rvis"=> fun i: U=> Bid.visits C (R₀ i).1 (R₀ i).2
local notation "Q"=> Cutoffs
variable (P:(j:Fin v)→Rowe C (s j))(x: C.book.Vector s)(R₀) -- explicit R₀
lemma TiltReveals {d' d:ℕ} (h:d'=d){F':Trial C} {v:Rowe C d'}(hp:Reveals C f F' v):Reveals C f F' (d:=d) (fun i=>Dash.Shot.Tilt C.book d' d h (v i)):=by subst d; exact hp
local notation "T!"=> outfits s R₀
include h
lemma exemplify (W:Fin v→Trial C)(ht:∀ i, Reveals C f (W i) (P i)) : ∀ i:Fin (v+n), Reveals C f ((Fin.append W (fun i=> Bid.visits C (R₀ i).1 (R₀ i).2)) i) (d:=(Fin.append s (fun i=> (R₀ i).1)) i) ((outfits s R₀ P) i):=by
    intro j; refine Fin.addCases (fun i=>?_) (fun i=>?_) j <;> unfold outfits
    · rw [Fin.addCases_left,Fin.append_left W (fun i=> Bid.visits C (R₀ i).1 (R₀ i).2)]; exact TiltReveals _ (ht i)
    rw [Fin.addCases_right,Fin.append_right W (fun i=>Bid.visits C (R₀ i).1 (R₀ i).2)]; exact TiltReveals _ (truth_sober h (R₀ i).2)
variable {φ:Filter Cutoffs}[φ.NeBot](hp:φ ≤ f.fuse)(ht:∀ i,Tendsto (P i) φ (𝓝 (x i)))
noncomputable def integrated (T:YM.Table C.book) :=F'.applyTo (fun z=> T.read z (Fin.append (fun i:Fin v=>⟨s i,x i⟩) R₀))
include H ht hp
lemma projected_smears (D':Fin v → Trial C)(hv:∀ i, Reveals C f (D' i) (P i)) : Tendsto (certificate (Fin.append D' (fun i=>Bid.visits C (R₀ i).1 (R₀ i).2)) F') φ (𝓝 (integrated F' s R₀ x T)):=by
    let x': (i:Fin v)→ Rowe C (s i):= fun i _=> x i; let u(i):= outfits s R₀ P i; let z(i):= outfits s R₀ x' i (0,0); have ht' (i:Fin (v+n)): Tendsto (u i) φ (𝓝 (z i)):=by
       refine Fin.addCases (fun i=> ?_) (fun i=>?_) i <;> dsimp only [u,z,outfits]
       · simp only [Fin.addCases_left]; exact (Dash.Shot.Tilt C.book _ _ ((Fin.append_left s (fun i=> (R₀ i).1) i).symm)).continuous_of_finiteDimensional.continuousAt.tendsto.comp (ht i)
       simp only [Fin.addCases_right]; exact tendsto_const_nhds
    have h: F'.applyTo (fun x=> T.value (Fin.append s (fun i=> (R₀ i).1)) x z)=integrated F' s R₀ x T:=by
       let K:= Fin.append s (fun i=> (R₀ i).1); have he: Fin.append (fun i=> (⟨s i,x i⟩:C.book.Token)) R₀=fun j=>⟨K j,z j⟩:=by
           funext j; refine Fin.addCases (fun i=> ?_) (fun i=>?_) j <;> try dsimp only [z,outfits]
           · rw [Fin.append_left (fun i=> (⟨s i,x i⟩:C.book.Token)), Fin.addCases_left]; exact (Dash.Shot.tilt ..).symm
           rw [Fin.append_right (fun i=> (⟨s i,x i⟩:C.book.Token)), Fin.addCases_right]; exact (Dash.Shot.tilt ..).symm
       unfold integrated; rw [he];rfl
    rw [← h]; exact earns ‹C.Makes› _ F' u z H.clean.mesh.integral (exemplify ‹C.Makes› s R₀ P D' hv) hp H.center ht' -- args
variable {w ζ}(Y:OPE.Package C w ζ D)(hG:G.Simple)(hf:∀ i,Slow C f (F i))
omit ht
include hG Y hf
lemma passes_limits (hpX:∀ i, ∀ᶠ k in atTop, ∃ P1, Reveals C f (code m k (F i)) (d:=s i) P1 ∧ Tendsto P1 φ (𝓝 (x i))) : Tendsto (fun u:Cutoffs=> jointS F' s F R₀ m u.1 u.2) φ (𝓝 (integrated F' s R₀ x T)) :=by
     obtain ⟨k,hk,h₁⟩:= ((eventually_ge_atTop ((∑ i:Fin v,s i)+∑ i:Fin n,(R₀ i).1)).and (eventually_all.mpr hpX)).exists; choose v' hv ht using h₁
     have hK:= projected_smears h F' s R₀ H v' x hp ht _ hv
     have he:= hK.sub ((entry_test (m:=m) h F' s F R₀ Y hG hf hk).mono_left hp); rw [sub_zero] at he; apply he.congr; intro u; exact sub_sub_cancel ..
-- Frame port supply. inherit ANY φ subfuse
variable {u:Cutoffs}
end YM.RG05Readout.Chalice
