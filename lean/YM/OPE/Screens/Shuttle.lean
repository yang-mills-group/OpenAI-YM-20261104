import YM.OPE.Screens.Takes
/-!
# Sublimit toolkit
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Shuttle
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Marker Local MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Book Book.Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open Drapery Backup Motion Extra.Multi Next.Rank.Station Cells
open Book.Tariff Playout.Rake Rhythm.Store Rhythm Next.UVStress Spec Cards
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Z : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] {G:Gauge}
    {H l m k b N p A t t' q d:ℕ}{Q: Rhythm I}{C:Family G}
set_option quotPrecheck false
variable {F:Extraction.Order} {S:Table C.book} {P:Q.Loom} (U:Final C F S)
local notation "μ!"=> C.S.a
local notation "L!"=> P.launch Q.limit
local notation "T!"=> C.S.gridPoint
variable {f f': Filter (ℕ×ℕ)}[f.NeBot] (h:f ≤ F.fuse)
variable {x:I→ Cover}{v:I→ C.book.Token}
    {W r' D'}(L:LogPackage C W r' D')
lemma periods : Tendsto Prod.snd F.fuse atTop:=tendsto_atTop.mpr fun i=>by rw [Extraction.Order.fused,Extraction.Order.late]; filter_upwards [F.per.cofinal.eventually_ge_atTop i] with p hp; exact Eventually.of_forall fun _=>hp
lemma gallery (hp:N ≥ k)(v: I→ Cover)(i:I): Trunk.lens C k p v N i = Cells.location C.S k N p (v i):= by unfold Cells.location Trunk.lens; rw [dif_pos hp]; exact Ribbons.vect C _ _ _ _ hp -- .. syntax
-- arbitrary term format helpful Epic.Exact.Spark pressure read
abbrev lobby {J:Type}[Fintype J](x:J→ Cover)(v:J→ C.book.Token)(V:ReadLabel C v)(k:ℕ): Cylinder C := register C k x (germ V)
def bill (x:I→ Cover)(v:I→ C.book.Token)(V:ReadLabel C v)(s:Finset I)(k:ℕ): Cylinder C:= lobby (fun j: s =>x j.val) (fun j:s=> v j.val) (fun j=>V j.val) k -- coercions into ghost instances
abbrev entering (z:C.label d)(N p:ℕ) : Config G (C.side N p)→ℂ := C.O N p z 0
abbrev stampEntry (d:ℕ)(z:ℕ×ℕ→ C.label d) : Cylinder C:=fun N p=>entering (z (N,p)) N p
lemma billL (V:ReadLabel C v)(s:Finset I) {U:Config G (C.side N p)} (hn:k ≤ N) : bill x v V s k N p U=∏ i∈ s,C.O N p (V i (N,p)) (Trunk.lens C k p x N i) U:=by
    unfold bill lobby; rw [germ_here]; simp_rw [gallery hn]; exact (prod_coe_sort s (fun i=> C.O N p (V i (N,p)) (Cells.location C.S k N p (x i)) U))
lemma lobbyL (V:ReadLabel C v){U: Config G (C.side N p)}(hn:k ≤ N): lobby x v V k N p U=∏ i,C.O N p (V i (N,p)) (Trunk.lens C k p x N i) U:= by unfold lobby; rw [germ_here]; simp_rw [gallery hn]
-- internal word combine from sign broadcast
lemma billJoin (V:ReadLabel C v)(s:Finset I)(k:ℕ)(N p)(i)(h:k ≤ N): lobby x v V k N p i = bill x v V s k N p i * bill x v V (univ\s) k N p i:=by
    rw [mul_comm,billL V _ h, billL V _ h,lobbyL V h, prod_sdiff (subset_univ s)]
include h U
-- needed support.T.Surface. Acquired when Full reps arrived
abbrev living (C: Family G)(b N p:ℕ)(q:Config G (C.side N p)→ℂ) := ∀ he:b≤N, Interior ((center C.S p he 0).chamber 0) q
lemma coming (x:Cover)(he: 8*‖T! k x‖ ≤ μ! b)(d:ℕ): ∀ᶠ i:ℕ×ℕ in f,∀ y:C.label d, living C b i.1 i.2 (C.O i.1 i.2 y (Cells.location C.S k i.1 i.2 x)):=by
    have ht:=largeMesh F|>.mono_left h
    filter_upwards [ht.eventually (near_center C b d U.room.cutoff),(periods.mono_left h).eventually (faraway C k x), ht.eventually_ge_atTop k] with i ht hp hn y hv; let t:= wrap (C.side k i.2) x; have hb:k ≤ i.1:=hn; unfold Cells.location; rw [dif_pos hb]; apply ht hv; rw [C.S.embeds_place,hp]; exact he -- let
lemma coming0 (b d:ℕ): ∀ᶠ i:ℕ×ℕ in f,∀ y:C.label d, living C b i.1 i.2 (entering y i.1 i.2):=by
    have he:= coming U h (0:Cover) (k:=b) (b:=b) (by rw [grid_zero]; simp [(C.S.a_pos _).le]) d; filter_upwards [he] with i hi y using (by unfold entering; rw [← location_origin (k:=b) (C:=C) (N:=i.1) (p:=i.2)]; exact hi y)
omit U
variable {hp₀:Fintype.card I > 0}
-- after N∈f build Slot interfaces, inputs may announced class equality
structure Adoption (C:Family G)(t:ℕ)(e:ℝ)(b:ℕ)(z:C.label b)(φ:Filter (ℕ×ℕ))(Q:ℕ×ℕ→ C.label b): Prop where
    tickets : ∀ᶠ i in φ,quota C b t i.1 i.2 (Q i) ≤ e
    wins : Tendsto Q φ (𝓝 z)
structure Starts (φ:Filter (ℕ×ℕ))(S:Table C.book)(v w:I→ C.book.Token)(V: ReadLabel C w): Prop where
    ongoing : S.classTokens ∘ w = S.classTokens ∘ v
    values (j:I): Tendsto (V j) φ (𝓝 (w j).2)
omit h in
lemma Starts.quiet {φ ψ:Filter (ℕ×ℕ)}{w:I→ C.book.Token}{V:ReadLabel C w}(h:Starts φ S v w V)(hp:ψ ≤ φ) : Starts ψ S v w V:= ⟨h.ongoing, fun j=>(h.values j).mono_left hp⟩ -- omit h, f
include U
lemma copy_stop {V:ℕ×ℕ→ C.label d} {x:ℝ} (he:∀ᶠ i in f, quota C d k i.1 i.2 (V i) ≤ x)(hp:C.ref d ≤ k): ∃ f',∃ y:C.label d, f'.NeBot ∧ f' ≤ f∧ Tendsto V f' (𝓝 y) :=by
    obtain ⟨P,hP,hQ⟩:= quota_stop C U.room.cutoff hp; obtain ⟨f',hh,hi,u,hA⟩:= finite_extract V (P*x) (𝓛:=f) (by filter_upwards [he, (largeMesh F|>.mono_left h).eventually_ge_atTop k] with i hi ht using (hQ i.1 i.2 (V i) ht).trans (mul_le_mul_of_nonneg_left hi hP)); exact ⟨_,u,hi,hh,hA⟩
end YM.OPE.Log.Trunk.Shuttle
