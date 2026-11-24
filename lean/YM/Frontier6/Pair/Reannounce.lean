import YM.Frontier6.Pair.Sublimits

/-! Lower-cost re-announcement of high-horizon primary cylinders along
any eventual plane sequence. Does not alter stencil or require convergence
of coordinates on whole mesh sequence. The detecting base at the earlier
raw-extraction step interprets all subsequent sublimits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Canvas
open Function Filter Lattice Wilson RG Labels Bid Work.G08 Finset Extra.Histories MergeProof MergeProof.Ribbons Next.UVStress Source
open Push.RelayDifference PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage Sublimits
open Extraction.Lease
open scoped BigOperators Topology Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{W:Worth}{F:Extraction.Order}{D e : ℕ}
variable (h:C.Makes) (hG:G.Simple)(ht:Stock.Tabs C.path.levels)
variable {u ψ:ℕ→ℝ}{r:ℕ→ℕ}{A:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable {hB:roomCost C.path.levels W} (hc: ColumnSteps C W) (hW:Scrim C W u ψ (near C.path.levels) (renal C.path.levels) (fly C.path.levels) r A)
variable (hF:Fridge C u (fly C.path.levels))
set_option quotPrecheck false
local notation "B"=> C.labels.level D
include h hc hG hW
lemma legacy_announce (he:e<D)(v:Rowe C D) (hb:tight C F v)(hv : ∀ᶠ i:ℕ×ℕ in F.fuse,
   shed B e ((C.factory D i.1 i.2).terminal.symm (v i))=0) : RawProtected C F (Bid.upper C v) e:= by
   let E (i:Cutoffs) := (C.factory D i.1 i.2).terminal.symm; let r:= C.ref D; let d:=D-e
   have hx : Slow C F v:=by
      intro ε hε; obtain ⟨a,ha⟩:= hb; exact ((show ∀ᶠ i:ℕ×ℕ in F.fuse, ‖v i‖≤a from ha).and ((cost_grows hε).eventually_ge_atTop a)).mono (fun i hi=>hi.1.trans hi.2)
   have hp : Slow C F fun i=>fee C.path.levels i.1:=by
      have ht:Note C.S (fee C.path.levels) 0:= ((futon C).powerN 2).swapP (by norm_num)
      intro ε hε; filter_upwards [(cutoff_grows F).eventually (ht.outweigh (Note.bell_exp C.S ε) hε)] with i hi
      exact le_trans (Real.norm_of_nonneg (ht.pos _|>.le)|>.le) hi
   let sessionW (i:Cutoffs) : ℂ:= (C.S.a i.1:ℂ)^d; let x: Rowe C D:= fun i=> (sessionW i)⁻¹ • v i
   have ha : dollar C F x:=by
      apply dollar_slow x|>.2
      refine (((hp.mul (Slow.const ((C.S.a r)^d)⁻¹)).mul (coords_slow v hx))).reduce (?_)
      filter_upwards [(cutoff_grows F).eventually_ge_atTop r,hv] with i hi hv
      let a:= C.S.a i.1; let c:= C.S.a r; have ha:0 < a:=C.S.a_pos _; have hu:0<c:= C.S.a_pos _
      change ‖E i (x i)‖≤ ‖_‖; rw [show E i (x i)= (sessionW i)⁻¹ • E i (v i) from (E i).map_smul ..,norm_smul,norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg ha.le]
      let L:= fee C.path.levels i.1; let M:= (B).coeffSize (v i); have hL:0 ≤ L:=zero_le_one.trans (fee_one ..); have hM:0 ≤ M:= size_nonneg ..
      change (a^d)⁻¹*‖E i (v i)‖ ≤ ‖L* (c^d)⁻¹*M‖
      rw [Real.norm_of_nonneg (by positivity)]; apply (mul_le_mul_of_nonneg_left (legacy_price C h hc hW.costs.cost hW.costs.back e he hi _ hv) (show 0 ≤ (a^d)⁻¹ by positivity)).trans
      change (a^d)⁻¹*(L*(a/c)^d*M) ≤ L* (c^d)⁻¹*M; apply le_of_eq; rw [div_pow]; field_simp
   obtain ⟨X,hX,y,b,hh,hK,hq⟩:=RawProtected.upper h hG x ha
   refine ⟨X,hX,y,b,hh,hK,hq.mono fun t ht=>ht.mono fun i he'=>fun o=>?_⟩
   let j:Cutoffs:= (F.mesh i,F.per t)
   rw [show unpriced C (Bid.upper C v) e j.1 j.2 o = unpriced C (Bid.upper C x) D j.1 j.2 o from ?_];exact he' o
   change ((C.S.a j.1:ℂ)^e • _)=(C.S.a j.1:ℂ)^D • C.O j.1 j.2 ((sessionW j)⁻¹ • v j) o; rw [ (C.linearO j.1 j.2 D o).map_smul,smul_smul,show (C.S.a j.1:ℂ)^D * (sessionW j)⁻¹ = _
      from (?_ : (C.S.a j.1:ℂ)^D * (sessionW j)⁻¹ = (C.S.a j.1:ℂ)^e)]
   · rfl
   have hc : (C.S.a j.1:ℂ)≠0:= Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne'
   unfold sessionW; rw [show D=e+d by unfold d; omega, pow_add]; field_simp

include ht hF
open Next.Extract Dash in
lemma legacy_sublimit {S T:Table C.book}{M:ℕ→Table C.book}{R:Bin T}{Y:DiffPlan S}(H:Base C F T M R S Y) {Y':DiffPlan S} (hY:Y'.Inclusions S)
   (he:e<D)(v:Rowe C D) (hb:tight C F v)(hv: ∀ᶠ i : ℕ×ℕ in F.fuse,
   shed B e ((C.factory D i.1 i.2).terminal.symm (v i))=0) {w:Filter (ℕ×ℕ)} [w.NeBot]
   (hw:w ≤ F.fuse) {x:C.label D} (hx:Tendsto v w (𝓝 x)) : S.project D x ∈ LinearMap.range (Y'.rise he.le):= by
   let p:= upper C v
   have hA:vet C F e (Bid.upper C v):= onions h ht hW hG hF (Bid.upper C v) (legacy_announce h hG hc hW he v hb hv) (Stencilled.upper h v) (Eventually.of_forall fun i=> C.continuousO ..)
   let z:= H.arrives.born
   have hp (i:Shot C.book) : Tendsto (uncurry (targetB (Bid.upper C v) i)) w (𝓝 (i.core T z x)):=
      (arcing ((i.ready z H.arrives.census.integral D).mono_left hw) hx).congr (fun _=> (upper_scan v i _ _).symm)
   obtain ⟨b,hb⟩:= matched_any Work.D01.answer Work.D02.answer h H.center R (H.carries e) (sober_upper _) hA hw hp
   obtain ⟨t,_,hh⟩:=brace (fun i=> snapshots i e) (fun i=> Shot.core i T z) (Filter.Tendsto.mono_left (H.pinned.p _).slides hw) (Bin.exactC R H.arrives.census.integral (H.pinned.p e) (H.pinned.q e)) (fun i=> (i.ready z H.arrives.census.integral _).mono_left hw) _ hb
   -- compare smooth Shots
   let Z : Live S := fun n v t => Test.smearing t (S.smooth_read H.clean.smooth v).continuousOn
   have hq (i:Shot C.book): i.core S Z t=i.core S Z x := Eq.trans ((show i.core T z t=i.core S Z t from faithful H.clean.sharp _ _).symm) ((hh i).trans (show i.core T z x=i.core S Z x from faithful H.clean.sharp _ _))
   let hs:= H.clean.basic.toSymmetric
   refine ⟨S.project _ t,S.field_ext hs (fun n q y hy=> ?_)⟩
   rw [hY.kernels he.le _ hy,MonitorOps.head S hs _ q hy,MonitorOps.head S hs _ q hy]
   let L(i:Fin n):C.book.Token:= ⟨(q i).1,S.representative _ (q i).2⟩
   let g (a : C.book.Token)(x:Points (n+1)):= S.read x (Fin.cons a L)
   refine (Test.unique_kernel (K:=g ⟨e,t⟩) (P:=g ⟨D,x⟩) ((S.smooth_read H.clean.smooth _).continuousOn) ((S.smooth_read H.clean.smooth _).continuousOn)).1 ?_ hy
   intro u; have ht:= hq (Shot.mk _ 0 (Fin.cons (α:=fun _=>C.book.Token) ⟨_,x⟩ L) u)
   change u.applyTo (fun y=>S.read y (update _ 0 (⟨e,_⟩:C.book.Token)))=u.applyTo (fun y=>S.read y (update _ 0 _)) at ht
   have he y : update (Fin.cons (α:= fun _=> C.book.Token) (⟨D,x⟩:C.book.Token) L) 0 y=Fin.cons y L := by simp
   rw [he,he] at ht; exact ht
end YM.Frontier6.Canvas
