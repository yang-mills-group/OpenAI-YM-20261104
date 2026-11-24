import YM.OPE.Short.Gap
/-!
# Placing finite stress words in the measuring geometry

Weak comparison along same X trajectory supplies actual correlations of
engineering-scaled stress components. Here only the vacuum direction is
queried at the output. All identities on the actual continuum separated
domain. The meter needn't be a pure dilation eigenbasis on physical slots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Short
open Orbits Orbits.Reader Nesting Nesting.Tree Function Filter Set Table Extraction Spec Climb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(X:Climb.Scaling S) (hG:G.Simple) (H:Pert.FirstExtension U X)
local notation "Q"=>U.sector.derivatives

abbrev extra {z : Empty}:S.Tag := nomatch z
abbrev gapPos(z:Empty):E4:=nomatch z
lemma tagged {I:Type}[Fintype I](v:I→S.Tag)(x:I→E4)(q:Viewers U)(hx:Injective x): whole (spectator U q) x (voices v) gapPos (voices (fun z=> (extra (z:=z):S.Tag))) = Orbits.moment (spectator U q) x (voices v):=by
       let T (q:Viewers U):=spectator U q
       have hv:Injective (beside x gapPos):=beside_distinct.mpr ⟨hx, injective_of_subsingleton _, fun i j=>nomatch j⟩
       let w:=Orbits.tags (stages (voices v) (voices (fun z=> (extra (z:=z):S.Tag))))
       have he:=Sparse.Undo.restrict (Sparse.momentIdentity (S:=S) (T q) (spectate U q) (spectate_respects U q)) (beside x gapPos) hv Sum.inl Sum.inl_injective w fun z hz=> ?_ -- parameter J infer? Sum.inl domain I implicit
       swap
       · rcases z with z|z; exact (hz z rfl).elim; cases z
       exact he

lemma vacuum (q:Viewers U)(o:E4)(m:ℕ)(u:Empty→S.Tag): Orbits.upon (spectator U q) m o gapPos (voices u) (S.unit m) = 1:=by -- n param?
    let T:=spectator U q; let e:Unit→S.Tag:= fun _=>⟨m,S.unit m⟩
    have h:=Sparse.Undo.restrict (Sparse.momentIdentity (S:=S) (spectator U q) (spectate U q) (spectate_respects U q)) (sole o) (injective_of_subsingleton _) (fun (_:Empty)=>()) (fun i=>nomatch i) e (fun j hj=>rfl)
    have ht :∀ (x:Empty→E4) (v:Empty→S.Tag), Orbits.moment (spectator U q) x (voices v:Labels S (degrees v))=1:=by
       intro x v
       rw [Orbits.observed]; unfold observe worded; rw [Table.readAt]
       have ht(n:ℕ)(hn:n=0)(f:Fin n→C.book.Token)(x:Points n): (spectator U q).read x f=1:=by subst n; exact (spectate U q).laws.trivial f x
       exact ht _ Fintype.card_eq_zero _ _
    change whole (T) (sole o) (voices e) gapPos (voices u)=1
    rw [Subsingleton.elim u (fun z=> (extra (z:=z):S.Tag))] -- bad syntax edit
    exact (tagged U e (sole o) q (injective_of_subsingleton _)).trans (h.trans (ht _ _))

include X U hG in
lemma vacuum_vector (q:Viewers U)(o:E4)(v:S.Field 0)(u:Empty→S.Tag): Orbits.upon (spectator U q) 0 o gapPos (voices u) v • S.unit 0=v:=by
    obtain ⟨c,rfl⟩:=unit_field U X hG zero_lt_four v
    rw [map_smul,vacuum U ..]; exact congr_arg (· • _) (mul_one c) -- c smul complex one

include X U hG in
lemma vacuum_common (q:Viewers U)(o:E4)(v:S.Field 0)(u:Empty→S.Tag): Orbits.upon (spectator U q) 0 o gapPos (voices u) v=Orbits.upon S 0 o gapPos (voices u) v:=by
   have h:= (vacuum_vector U X hG q o v u).trans (vacuum_vector U X hG none o v u).symm
   exact smul_left_injective ℂ (S.alive 0 U.room.kernel.laws) h -- R omitted? use U
open Pert
abbrev Picture (I:Type):= I→Axis×Axis
variable {I:Type}[Fintype I](ab:Picture I)
def stressTag (i:I):S.Tag:=⟨4,U.sector.energy (ab i).1 (ab i).2⟩
def freeTarget: I → (Maxwell.freeTable C.labels).Tag:= fun i=>⟨4,freeStress C.labels (ab i).1 (ab i).2⟩

abbrev exponent (I:Type)[Fintype I]:ℕ:= 4*(Fintype.card I)

def harmonic(r:ℝ)(x:I→E4)(o:E4)(i:I):=r•x i+o
def frame (x:I→E4): Points (Fintype.card I) := points (x ∘ runNames I)
lemma framed : ContDiff ℝ ∞ (frame (I:=I)):=by unfold frame points; fun_prop
lemma occupancy (x:I→E4)(hx:Injective x):frame x∈conf _:=hx.comp (runNames I).injective

section Conversion
include X U
lemma zoom (x:I→E4)(o:E4)(k:ℕ)(hx:Injective x): ((↑((X.r k)^(exponent I)):ℂ):ℂ) • Orbits.moment S (harmonic (X.r k) x o) (voices (stressTag U ab)) = Ward.disc (scaledPhysical X U.sector.energy k (fun _=>⟨0,0⟩) (fun _=>true) (ab ∘ runNames I)) (X.r k • frame x):=by
    let r:=X.r k
    have ho : Injective (fun i=>r• x i):=by rintro i j hh; exact hx ((smul_right_injective E4 (X.positive k).ne') hh)
    let v:=voices (stressTag U ab)
    let z:Labels S (degrees (stressTag U ab)):=fun j=> (↑(r^4):ℂ) • v j
    have hz:z=fun j=> (↑(r^4):ℂ) • v j:=rfl
    have h_m: scaledPhysical X U.sector.energy k (fun _=>⟨0,0⟩) (fun _=>true) (ab ∘ runNames I)= Orbits.tags (d:=degrees (stressTag U ab)) z ∘ runNames I:=by ext1 j; simp [z,scaledPhysical,r,tags,voices,stressTag,degrees,v]; rfl
    let m:= Orbits.moment (S:=S) S (d:=degrees (stressTag U ab)) (fun i=> r•x i)
    rw [show ((Orbits.moment S (harmonic (X.r k) x o)) v) = m v from carrying (T:=S) (U.room.kernel) (a:=v) ho o]
    rw [h_m]; unfold Ward.disc
    rw [show X.r k • frame x= points ((fun i=>r• x i) ∘ runNames I) from by apply (WithLp.ofLp_injective ..) (?_); rfl]
    change ((↑(r^(exponent I)):ℂ):ℂ) • m v = m z
    rw [hz, m.map_smul_univ]; unfold exponent; rw [pow_mul, Finset.prod_const, Finset.card_univ, Complex.ofReal_pow]

variable {K:Set (I→E4)}(hK:IsCompact K)(hs:∀ x∈K, Injective x)
include H hK hs
omit R
lemma comparable {ε:ℝ}(he:0<ε): ∀ᶠ k in atTop, ∀ x∈K, ∀o:E4,
    ‖(↑((X.r k)^(exponent I)):ℂ) • Orbits.moment S (harmonic (X.r k) x o) (voices (stressTag U ab)) - Orbits.moment (Maxwell.freeTable C.labels) x (voices (freeTarget (C:=C) ab))‖ ≤ ε:=by
    let tags (i:Pert.Slots (Fintype.card I)) := (⟨0,0⟩: (Maxwell.freeTable C.labels).Tag)
    let K':=frame '' K
    let iab:= ab ∘ runNames I; let use:=fun _:Fin (Fintype.card I)=>true
    let f:=Pert.freeWithStress C.labels tags use iab
    let Fx(k:ℕ) (x):=Ward.disc (scaledPhysical X U.sector.energy k tags use iab) (X.r k • x)
    have h:=H.jets (K:=K') (ε:=ε) (Fintype.card I) 0 tags use iab (hK.image (f:=frame) (framed.continuous)) (Set.image_subset_iff.mpr (fun a ha=> occupancy a (hs a ha))) he
    filter_upwards [h] with k hk x hx o; specialize hk _ (Set.mem_image_of_mem frame hx)
    change ‖iteratedFDeriv ℝ 0 (Fx k) (frame x)-iteratedFDeriv ℝ 0 (Ward.disc f) (frame x)‖ ≤_ at hk
    let g:=iteratedFDeriv ℝ 0 (Fx k) (frame x)-iteratedFDeriv ℝ 0 (Ward.disc f) (frame x)
    let u: Fin 0→Points (Fintype.card I):=fun _=>0
    have heq:g u= Fx k (frame x)-Ward.disc f (frame x):=by change (iteratedFDeriv ℝ 0 (Fx k) _) u - (iteratedFDeriv ℝ 0 (Ward.disc f) _) u = _; rw [iteratedFDeriv_zero_apply,iteratedFDeriv_zero_apply]
    calc _ = ‖g u‖ := congr_arg₂ (fun a b:ℂ=>‖a-b‖) (zoom U X ab x o k (hs x hx)) (?_ : Orbits.moment (Maxwell.freeTable C.labels) x (voices (freeTarget (C:=C) ab)) = Ward.disc f (frame x))|>.trans (congr_arg norm heq.symm)
         _ ≤ _:= (g.le_opNorm u).trans ((by simpa using hk))
    change (Maxwell.freeTable C.labels).useAt (Maxwell.freeTable C.labels) (points (x ∘ runNames I)) (fun i=>_) = (Maxwell.freeTable C.labels).useAt (Maxwell.freeTable C.labels) (points (x ∘ runNames I)) (Pert.freeWithStress C.labels _ _ _)
    apply congr_arg₂ ((Maxwell.freeTable C.labels).useAt (Maxwell.freeTable C.labels)) rfl; funext c; simp [f,freeWithStress,use,iab,freeTarget,tags,Orbits.tags,stressTag,Function.comp_def,degrees,voices]
end Conversion
end YM.OPE.Short
