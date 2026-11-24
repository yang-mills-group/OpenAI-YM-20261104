import YM.Integration.WilsonSeparatedOriginalSlabWatchSupport

/-! Identification of all exterior grid sites on the same thermodynamic and short-distance filter. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchPlacement
open Function Filter Set Wilson Lattice RG Source Extra.Histories Extraction Spec Cells OPE OPE.Orbits OPE.Cards
open Next.UVStress RG05Readout.Native RG05Readout.Pulse WilsonSeparatedOriginalSlabWatchCorners WilsonSeparatedOriginalSlabWatchSupport
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{I:Type}[Fintype I]

theorem periods (f:Extraction.Order):Tendsto (Prod.snd:ℕ×ℕ→ℕ) f.fuse atTop:=
  tendsto_atTop.mpr fun i=>show f.late (fun _ p=>i≤p) from (f.per.cofinal.eventually_ge_atTop i).mono fun _ hi=>Eventually.of_forall fun _=>hi

theorem fixed (W:Watch C):∀ᶠ k:ℕ×ℕ in f.fuse,∀i:Fin W.n,C.S.place (W.among k.1 k.2 i)=fixedSites W i:=by
  let X:=tag (C.S.a W.t) W.x
  have roomP:= (periods f).eventually (Extraction.room C.S (isCompact_singleton (x:=X)))
  filter_upwards [roomP,(OPE.Cards.largeMesh f).eventually_ge_atTop W.t] with k roomP titled
  have inside:X∈Inside C.S k.2 W.n:=roomP (mem_singleton X)
  have inFund:X∈Fund C.S k.2 W.n:=fun i a=>⟨(inside i a).1,(inside i a).2.le⟩
  obtain ⟨q,hq,_⟩:=Extraction.corners (N:=W.t) inFund
  have addr:address (C.S.a W.t) X=fun i=>lift (q i):=hq
  rw [show address (C.S.a W.t) X=W.x from address_matched (C.S.a_pos _) _] at addr
  intro i
  have site:lift (wrap (C.S.side W.t k.2) (W.x i))=W.x i:=by rw [congr_fun addr i,wrap_lift]
  rw [Watch.among,Cells.location,dif_pos titled,C.S.embeds_place]
  exact congrArg (C.S.gridPoint W.t) site

theorem chart (W:Watch C):∀ᶠ p:ℕ×ℕ in f.fuse,∀x:I→Site (C.side p.1 p.2),
    WilsonSeparatedOriginalSlabWatchCorners.corners W p.1 p.2 x=joined W (C.S.place ∘ x):=by
  filter_upwards [fixed (f:=f) W] with p held
  intro x
  apply PiLp.ext;intro i
  change C.S.place (placed W p.1 p.2 x (runNames _ i))=Sum.elim (C.S.place ∘ x) (fixedSites W) (runNames _ i)
  cases runNames (Arms (I:=I) W) i with
  | inl _=>rfl
  | inr j=>exact held j

theorem banded (W:Watch C)(k:ℕ){r:ℝ}(rp:0<r)(Ψ:Wave I)(g:Body)(A:Set (Cloud I))(enc:tsupport Ψ.val⊆A):
    ∀ᶠ p:ℕ×ℕ in f.fuse,∀x:I→Site (C.side p.1 p.2),WilsonSeparatedOriginalSlabPhysicalBox.row C k r Ψ g (C.S.place ∘ x)≠0 →
      WilsonSeparatedOriginalSlabWatchCorners.corners W p.1 p.2 x∈band W k r A:=by
  filter_upwards [chart (f:=f) (I:=I) W] with p site
  intro x live
  rw [site];exact registered W k rp Ψ g _ A enc live

end YM.Integration.WilsonSeparatedOriginalSlabWatchPlacement
