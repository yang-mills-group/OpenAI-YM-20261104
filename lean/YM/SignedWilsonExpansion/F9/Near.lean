import YM.SignedWilsonExpansion.F9.Popcorn
/-! # Production lights equality at the indicated exact positions

In particular, these point basis members, kept on their *own* physical tilt,
work after normalization by the offshell solver. The actual forecast used in
file computations can be compared through any fixed order with this one. This
ticket at inversion spends no spurious power of length; it is finite and EXACT.
-/
set_option autoImplicit false
set_option maxHeartbeats 780000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa.StationA
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Matrix
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost FVA2
open Cloth XSpace
open PertExtension PertExtension.Orb FormalOPE FormalOPE.RG10 FormalOPE.RG10.InversionWard
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical ENNReal InnerProductSpace
variable {G:Gauge}{H:Hol G}{h i j k a m r d n l:ℕ}{F:Frame G h}{x:Label G h}{P:Period} {s:Signed} {ι:Type*}
section forecast
variable (A:∀ d, XSpace.Survey G H d) (R:∀ d, Rays G d H)(L:Frames G)
def payments (d:ℕ):= (R d).fitsAt_support.choose
def CeilingQ (P:Period)(h b:ℕ): Prop:=∀ i≤h, FitsIn (payments R i) P.side ∧ cord (payments R i)≤b
lemma casingP (h:ℕ):∃ B:ℕ,∀ b:ℕ,B≤b→∀ P:Period,b≤ P.side.val→ CeilingQ R P h b:=by
   choose x H using fun i=> large_fits (payments R i); let f(i:ℕ):= max (x i) (cord (payments R i)); refine ⟨(Finset.Iic h).sup f,fun b a n y i h=> ⟨?_,?_⟩⟩; have hx: f i≤ b:= (Finset.le_sup (f:=f) (Finset.mem_Iic.mpr h)).trans a; exact H i n.side (((le_max_left ..).trans hx).trans y); exact (le_max_right ..).trans ((Finset.le_sup (f:=f) (Finset.mem_Iic.mpr h)).trans a)
lemma CeilingQ.down {b:ℕ}(q:CeilingQ R P h b)(v:d≤h):CeilingQ R P d b:=fun i a=> q i (a.trans v)
lemma CeilingQ.up {b:ℕ}(q:CeilingQ R P h b)(e:b≤d):CeilingQ R P h d:=fun i a=> ⟨(q i a).1, (q i a).2.trans e⟩ -- shadow
abbrev swingColumn (T:P.Tree)(x:P.Sites)(w:ℕ): Label G w →ₗ[ℂ] Bare.Series T G:= Bare.column T (A w) x ∘ₗ projector G w
abbrev tag_name (L:Frames G)(x:(L.level h).Index):= (L.level (wt (L.level h) x)).basis (downL L ((L.level h).bound x) x (le_refl _))
def lampTurn (T:P.Tree)(x:P.Sites)(s:Signed)(y:(L.level h).Index): Bare.Series T G:= swingColumn A T x _ (Labels.tensor s.ortho (tag_name L y))
def lamp (T:P.Tree)(x:P.Sites)(y:(L.level h).Index):= swingColumn A T x _ (tag_name L y)
variable (T:P.Tree)(x:P.Sites)(z:h≤k){b:ℕ}(hv:CeilingQ R P h b)(hp:2*b<separation x (-x))
lemma known (y:(L.level h).Index): tag_name L y∈ Grade (wt (L.level h) y,wr (L.level h) y):=by
    let F:=L.level h; let d:=wt F y; let i:=downL L (F.bound y) y (le_refl d); let T':=L.level d; rw [← show T'.grades i= (wt (L.level h) y, wr (L.level h) y) from down_grade L (F.bound y) y (le_refl d)] -- motive
    exact T'.pure i
include hv hp
lemma spin_lamp (s:Signed)(y:(L.level h).Index): SameV T x b (requesting T x k (rotate s k (fetch H A R z (L:=L) y))) (lampTurn A L T x s y):= by
    let F:=L.level h; let d:=wt F y; let D:=F.bound y; let i:=(downL L D y (le_refl _)); let hW:wr F y≤ d:= (congr_arg Prod.snd (down_grade L D y (le_refl d))).symm.trans_le (value_le (L.level d) i)
    unfold fetch; rw [Cloth.uprights,paid_ascent]; exact settled T (A d) (R d) x s _ (known L y) ((L.level d).realForm i) hW ((R d).fitsAt_support.choose_spec) (hv _ D).1 b (hv _ D).2 hp
omit hv hp
private lemma own_name (d h : ℕ)(x:(L.level h).Index)(w: wt (L.level h) x=d): d ≤ h:=w ▸ (L.level h).bound x
lemma at_tile (s:Signed)(x:P.Sites)(y:(L.level h).Index)(w:wt (L.level h) y=d): lampTurn A L T x s y= swingColumn A T x d (Labels.tensor s.ortho ((L.level d).basis (downL L (own_name L _ _ y w) y w.le))):=by subst d; rfl
-- turn acts with true per-level matrix. rewrite as per-d algebra over ℂ; all mixed lower fields have been paid, but h-index survives at this production rank. Project at own direction y.
private lemma landlord (y:(L.level h).Index) (d:ℕ)(w:wt (L.level h) y=d) (s:Signed):
    lampTurn A L T x s y= ∑ a:(L.level h).Index, realM (L.level h) s a y • lamp A L T x a:=by
    let F:= L.level h; let Z:=L.level d; let i':= own_name L d h y w; let i:=downL L i' y w.le; have hz:upL L i' i=y:=up_down ..; let A':=lamp (h:=h) A L T x; let X':=swingColumn A T x d; rw [at_tile A L T s x y w]; let Y:=X' ∘ Z.basis
    have ht:wt Z i=d:=(congr_arg Prod.fst (down_grade L i' y w.le)).trans w
    have hA (j:Z.Index)(he:wt Z j=d): Y j=A' (upL L i' j):=by
       have hi : wt F (upL L i' j)=d:= (congr_arg Prod.fst (up_grade L i' j)).trans he
       let L':= upL L i' j; have h0 (f:(L.level h).Index): lampTurn A L T x 1 f=A' f :=by unfold A' lamp lampTurn; rw [show Signed.ortho 1=1 from map_one Signed.inclusionO,tensor_one]
       rw [← h0, at_tile A L T _ x _ hi, show Signed.ortho 1=1 from map_one Signed.inclusionO,tensor_one, show downL L i' (upL L i' j) hi.le = j from up_faith L i' (up_down ..)]; rfl
    have hw:= spectate_weight L s i' i ht A' Y hA; rw [hz] at hw; rw [hw]
    let P:= tensor s.ortho (Z.basis i)
    change X' P= _; nth_rw 1 [← Z.basis.sum_repr P]; rw [map_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [map_smul, ← real_scalar_eq]; change (Z.coords P j) • _ = _; rw [show Z.coords P j= Complex.ofReal (bleached Z s.ortho j i) from (?_)]; try rfl
    unfold P; rw [← Z.act_coords,Z.coords_basis]; exact bleach_even ..
include hp hv
lemma dressed (y:(L.level h).Index): SameV T x b (requesting T x k (notesT H A R z (L:=L) y)) (lamp A L T x y):=by
    let F:= L.level h; let u:Signed→ Module.End ℝ (Cloth G k):= fun s=> rotate s k; let f:= fetch H A R z (L:=L); let a:ℝ:=Fintype.card Signed; let q:= a⁻¹; let L':= lamp A L T x (h:=h); let t:=requesting (G:=G) T x k
    let w(s):= faux F f u s y; have hw(s:Signed): SameV T x b (t (w s)) (L' y):=by
        let v(i):=lampTurn A L T x s i (h:=h); let i(a b):= realM F s⁻¹ a b; let V:= ∑ j:F.Index, i j y • v j; let X(j:F.Index):=u s (f j)
        have hV(j:F.Index): SameV T x b (t (X j)) (v j):= spin_lamp A R L T x z hv hp s j
        have ht : V=L' y:=by
           have he(v':F.Index): v v'=∑ a:F.Index,realM F s a v' • L' a:= landlord A L T x v' _ rfl s
           unfold V; simp_rw [he,Finset.smul_sum,smul_smul]; rw [Finset.sum_comm]; have hz (a:F.Index) : ∑ x:F.Index, (i x y * realM F s a x) = realM F 1 a y:=by
              rw (occs:=.pos [1]) [← mul_inv_cancel s] -- syntax
              rw [realM_turn]; exact Finset.sum_congr rfl fun _ _=>mul_comm ..
           simp_rw [←Finset.sum_smul,hz,realM_id]; simp [ite_smul]
        rw [← ht]; change SameV _ _ b (t (∑ j:F.Index, i j y • X j)) _; rw [map_sum]; simp_rw [map_smul]; exact SameV.sumP fun j _=> (hV j).real_fee _
    have ha: (∑ s:Signed, q • L' y)= L' y:= by rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ (by positivity),one_smul]
    change SameV T x b (t (q • ∑ s,w s)) (L' y); rw [← ha,Finset.smul_sum,map_sum]; simp_rw [map_smul]; exact SameV.sumP fun j _=>(hw j).real_fee _
omit hv hp
-- finite simultaneous price in lattice units (no upper period phase). `Aid` closed under scaling,
-- powers and products of these too.
lemma lamp_permit (y:(L.level h).Index): let i:= wt (L.level h) y; lamp A L T x y=requesting T x _ (permitT (A i) (projector_grade (known L y))):=by
   intro i; set Z':=downL L ((L.level h).bound y) y (le_refl i); have hm: (L.level i).grades Z'= _:= down_grade L ((L.level h).bound y) y (le_refl i); exact (pinwheel T _ (projector_grade (known L y)) (fixed_color _ ((L.level i).realForm Z')) x (A i) ((congr_arg Prod.snd hm).symm.trans_le (value_le (L.level i) Z'))).symm
lemma light_cap (h k:ℕ)(p:h≤ k):∃ B:ℕ, ∀ {P:Period}(T:P.Tree)(x y:P.Sites)(v:ℕ), v+B<separation y x→ v+B<separation y (-x) → ∀ d≤h,∀ i:(L.level d).Index,
      Aid T x v (lamp A L T y i)∧ Aid T x v (requesting T y k (Nest (L:=L) H A R k d i)):=by
    let S:= (d:Fin (h+1)) × (L.level d.val).Index
    choose B p using fun p:S=> Aid.leased (permitT (A _) (projector_grade (known L p.2))); choose C q using fun p:S=> Aid.leased (Nest (L:=L) H A R k p.1 p.2)
    let v:= Finset.univ.sup (fun x:S=>max (B x) (C x)); refine ⟨v,fun T x y b hx hy d hz i=>?_⟩ -- implicit binder
    let n:S:=⟨⟨d,Nat.lt_succ_of_le hz⟩,i⟩; have hu: max (B n) (C n)≤ v:= Finset.le_sup (f:=fun x:S=>max (B x) (C x)) (Finset.mem_univ n); have he: B n ≤ v:= (le_max_left ..).trans hu; have ht:C n≤v:=(le_max_right ..).trans hu; refine ⟨?_,q n _ T y x b (by omega) (by omega)⟩; rw [lamp_permit]; exact p n _ T y x b (by omega) (by omega)
end forecast
end YM.WilsonCoeffUV.Mer.Xa.StationA
