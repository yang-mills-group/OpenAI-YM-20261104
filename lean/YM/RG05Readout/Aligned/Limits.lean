import YM.RG05Readout.Aligned.Moving

/-!
# Read calibrated limit columns along SAME extraction

Output from Pickup in actual normalized master columns, along any
of these sublimits. Along ordered mesh x period before m-level prices
used. Allows probing continuum by any viewer and displaced configurations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Aligned
open Filter Topology Set Function Lattice Wilson Extraction Source OPE
open MergeProof Accent Ribbons PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Next.Rank Bid Cells Word Table Orbits
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (U:Spec.Final C f S) {H:Worth} {D r} (L:Package C H r D) {hC:C.Makes}
    {I J :Type}[Fintype I][Fintype J]
    {β:Filter (ℕ×ℕ)}
    {d K k m j:ℕ} {y E:ℝ}
set_option quotPrecheck false

/-- Actual unselected or selected observer on arbitrary original representatives.
Not tied to the choice `representative`. -/
lemma view_classes {z:I→E4} (q:I→C.book.Token)(hQ:Injective z) (W:Viewers U):
      OPE.observe (spectator U W) z q= Orbits.moment (d:=fun i=>(q i).1) (spectator U W) z (fun i=> S.project _ (q i).2) := by
    let T:=spectator U W
    unfold OPE.observe worded; rw [T.readAt]; let v:= q ∘ runNames I
    have he:(fun i=>S.classTokens (v i))= tags (S:=S) (d:=fun i=>(q i).1) (fun i=> S.project _ (q i).2) ∘ runNames I:=by
       funext i; unfold classTokens tags; rfl
    exact (S.at_project T (spectate U W).laws.toSymmetric (spectate_respects U W) (runs_conf.mpr hQ) v).symm.trans (congr_arg _ he)

lemma whole_classes (p:I→ C.book.Token)(q:J→ C.book.Token)
    (x:I→E4)(y:J→E4)(hx:Injective (OPE.beside x y))(s:Viewers U) :
    OPE.observe (spectator U s) (OPE.beside x y) (OPE.beside p q)=
       Orbits.whole (spectator U s) x (fun i=>S.project _ (p i).2) y (fun j=> S.project _ (q j).2) := by
    rw [view_classes U _ hx s, Orbits.whole]
    let P:=OPE.beside p q
    let v(u:I⊕J):= P u|>.1
    let w:= Sum.elim (fun i=>(p i).1) (fun j=>(q j).1)
    let V:Labels S v:= fun i=> S.project (v i) (P i).2
    let X:Labels S w:= stages (fun i=> S.project _ (p i).2) (fun j=> S.project _ (q j).2)
    change Orbits.moment (spectator U s) (OPE.beside x y) V= Orbits.moment (spectator U s) (OPE.beside x y) X
    rw [Orbits.observed,Orbits.observed]
    apply congr_arg (OPE.observe _ (OPE.beside x y))
    funext i; cases i<;> rfl

variable (W:Windows C hC β) (a:I→ℕ)

def columns (j:ℕ)(v:∀ i,C.label (a i)) : Labels S a:=fun i=> W.physical S (a i) j (v i)
def originals (j:ℕ)(v:∀ i,C.label (a i)) : I→ C.book.Token:=fun i=>⟨a i,W.ref (a i) j (v i)⟩
variable (v:∀ i,C.label (a i)){x:I→ Cover}
set_option quotPrecheck false
local notation "Ξ"=> originals W a j v
variable {A c t b l:ℕ}
variable {Z:J→ C.book.Token}{B:ℕ×ℕ→ C.label d}{e:J→ℝ}{X':J→E4}
include U
/-- Exterior readings at any of these limits, *of the actual masters*. -/
lemma towards [β.NeBot](hv:β ≤ f.fuse)(hs:Org.Grill C f)
    (u: C.label d) (hb:Tendsto B β (𝓝 u)) (hX:b≤ j)
    (hY:∀ᶠ i:ℕ×ℕ in β, Cards.PaidAt C.S i.1 i.2 K (C.beta i.1 i.2)
            (2*(stakes C K k / markRadius C d j))
            (product hC i.1 i.2 j x a v - C.O i.1 i.2 (masterRef hC d j i.1 i.2 (B i)) 0))
    (hx:Screen (C.S.gridPoint j ∘ x))(hGem:Apart (2*C.S.a l) X')(hE:ApartFrom (2*C.S.a b) (sole (0:E4)) X') (hΓ:Injective (OPE.beside (C.S.gridPoint j ∘ x) X'))
    (hQ: Cards.Hall C.S b l K c A 1 (Fintype.card J)) (hD: OPE.Prepared (C:=C) Z f A e) (s:Viewers U):
    let X:= (fun i=> S.project (Z i).1 (Z i).2 : Labels S (fun i=>(Z i).1))
    ‖whole (spectator U s) (C.S.gridPoint j ∘ x) (columns (S:=S) W a j v) X' X -
       upon (spectator U s) d 0 X' X (W.physical S d j u)‖ ≤
          2*(stakes C K k / markRadius C d j)*(∏ i,e i):=by
    let Q := originals W a j v
    let F:= C.S.gridPoint j ∘ x
    let g (w:ℕ×ℕ):=masterRef hC d j w.1 w.2 (B w)
    let Z' : ReadLabel C (originals W a j v):=fun i w'=> masterRef hC (a i) j w'.1 w'.2 (v i)
    let f' := W.ref d j u
    have hR(i): Tendsto (Z' i) β (𝓝 (Q i).2) := W.ref_tend (a i) j tendsto_const_nhds
    have he:= RG05_viewing (A:=2*(stakes C K k / markRadius C d j)) (P:=g) U hs hX hx hGem hE hΓ hQ hv (W.ref_tend d j hb) Z' hR (hY.mono ?_) hD
    swap
    · intro i hi; rw [show Cards.register C j x (germ Z') i.1 i.2=product hC i.1 i.2 j x a v from ?_]; exact hi
      exact funext fun u=> germ_here Z' x i.1 i.2 j u
    intro X
    let t:= spectator U s
    let g':= sole (0:E4); let L':= OPE.beside g' X'
    let M:= viewing U (OPE.beside F X') (OPE.beside Q Z)-viewing U L' (OPE.beside (sole (⟨d,f'⟩:C.book.Token)) Z); have hx:Injective L':=by
      exact hE.together (mul_nonneg zero_le_two (C.S.a_pos _|>.le)) (injective_of_subsingleton _) (hGem.coin (mul_nonneg zero_le_two (C.S.a_pos _|>.le)))
    have ht: glance U s M=whole t F (columns (S:=S) W a j v) X' X-upon t d 0 X' X (W.physical S d j u) := by
      unfold M; rw [map_sub,glance_sees U s _ _ hΓ,glance_sees U s _ _ hx]
      refine congr_arg₂ (fun x y:ℂ=>x-y) (?_ : OPE.observe t (OPE.beside F X') (OPE.beside Q Z)=_) ?_
      · exact whole_classes U Q Z F _ hΓ s
      exact whole_classes U (sole _) Z (sole 0) _ hx s
    rw [← ht]
    exact (glance_bound U _ _).trans (he)


open Next.UVStress
local notation "κ"=>2*(stakes C K k / markRadius C d j)
omit U

/-- Actual ordered sublimit of labelled *value* report. Includes a
concrete sequence of reports computed from true aligned density. -/
structure Sublimit (W:Windows C hC β) (L:Package C H r D) (a:I→ℕ)(v:∀ i,C.label (a i))
    (d K k m j:ℕ)(y E:ℝ)(x:I→ Cover)(u:C.label d) : Prop where
    along : ∃ Q:ℕ×ℕ→ C.label d, Tendsto Q β (𝓝 u) ∧
       ∀ᶠ i:ℕ×ℕ in β, ∃ h: Journey hC H D d K k m j i.1 i.2 a x v y E, h.payload hC= Q i

section selection
variable {hC:C.Makes}
include L
lemma reports_available {𝓤 : Ultrafilter (ℕ×ℕ)} {W : Windows C hC (𝓤:Filter _)}
    {b:I→ℝ}{v:∀ i,C.label (a i)}(hm:C.ref d ≤ m)(hv:(𝓤:Filter _)≤ f.fuse)
    (h: IssueAt hC f L a b d K k m j y E)
    (hp:Plot C k m j x) (hx:∀ i,(C.labels.level (a i)).coeffSize (v i) ≤ b i):
    ∃ u:C.label d,Sublimit W L a v d K k m j y E x u:=by
    let X (i:ℕ×ℕ) := Journey hC H D d K k m j i.1 i.2 a x v y E
    let Z i:= if hg:Nonempty (X i) then Journey.payload hC hg.some else 0
    have he := (h.program x hp).filter_mono hv
    obtain ⟨s,hs,hr⟩:= quota_stop C hC hm
    let Y:= C.labels.level d
    -- payload re-normalization occurs only at FIXED m,j in this limit
    obtain ⟨u,hu⟩:=bounded_ulim (𝓤:=𝓤) Z
      ((C.S.a j^d)⁻¹ * Extra.Histories.Charts.ingress C j * Fintype.card Y.Index * (s*(2*E))) (by
        filter_upwards [he,(Cards.largeMesh f|>.eventually_ge_atTop j).filter_mono hv ] with i hi he
        obtain ⟨p,hp'⟩:= hi v hx
        have hp' := (hp' p.some).1; have hf : Z i=p.some.payload hC:=dif_pos p; rw [hf]; let x:= (p.some.payload hC); let a:=masterRef hC d j i.1 i.2 x
        let K:= Extra.Histories.Charts.window C hC d j i.1 i.2
        have hw:‖a‖ ≤ s*(2*E):= (hr _ _ a (m.le_succ.trans (hp.last.trans he))).trans (mul_le_mul_of_nonneg_left hp' hs)
        have hz:Y.coeffSize a ≤ (Fintype.card Y.Index:ℝ)*(s*(2*E)):= by refine le_trans ?_ (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)); simpa only [YM.Labels.Frame.coeffSize,nsmul_eq_mul] using Pi.sum_norm_apply_le_norm (G:=fun _:Y.Index=>ℂ) a
        have ht := Extra.Histories.Charts.incoming C hC d i.1 i.2 j a
        let β := Extra.Histories.Charts.ingress C j; have hB:0 ≤ β:= zero_le_one.trans (Extra.Histories.Charts.ingress_one ..)
        have hQ: K a=((C.S.a j:ℂ)^d) • x:=window_masterRef ..
        let f:= (((C.S.a j:ℂ)^d)⁻¹); have hA:x=f • K a:=by rw [hQ,smul_smul,show f*((C.S.a j:ℂ)^d)=1 from inv_mul_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')),one_smul]
        have h0 : ‖f‖=(C.S.a j^d)⁻¹:= by unfold f; simp only [Complex.norm_pow,norm_inv,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos _).le]
        change ‖x‖ ≤ _; rw [hA,norm_smul]; apply le_trans (mul_le_mul_of_nonneg_left ((Extra.Histories.Size.norm_le ..).trans (ht.trans (mul_le_mul_of_nonneg_left hz hB))) (norm_nonneg _))
        rw [h0]; dsimp only [β,Y]
        exact le_of_eq (by ring))
    exact ⟨u,Z,hu,he.mono (fun i hi => ⟨((hi v hx).1).some, (show Z i=(hi v hx).1.some.payload hC from dif_pos (hi v hx).1).symm⟩)⟩ -- parentheses packaging
end selection
variable {b':I→ℝ}
include U

lemma charged [β.NeBot] (s:Org.Grill C f) (hf:β ≤ f.fuse) (hi: IssueAt hC f L a b' d K k m j y E)
    (hp:Plot C k m j x) (u:C.label d)(h:Sublimit W L a v d K k m j y E x u)
    (hΓ:∀ i,(C.labels.level (a i)).coeffSize (v i) ≤ b' i)
    (hB:b≤j)(hx:Screen (C.S.gridPoint j ∘ x))(hGem:Apart (2*C.S.a l) X')
    (hE:ApartFrom (2*C.S.a b) (sole (0:E4)) X') (hJ:Injective (OPE.beside (C.S.gridPoint j ∘ x) X'))
    (hQ: Cards.Hall C.S b l K c A 1 (Fintype.card J)) (hD: OPE.Prepared (C:=C) Z f A e)
    (s':Viewers U):
    let V:= (fun i=> S.project (Z i).1 (Z i).2 : Labels S (fun i=>(Z i).1))
    ‖Orbits.discrepancy (spectator U s') d (C.S.gridPoint j ∘ x) 0 (columns (S:=S) W a j v) (W.physical S d j u) X' V‖ ≤
       κ*(∏ i,e i):=by
   intro V; obtain ⟨f,h,hX⟩:= h.along; apply towards U W a v hf s u h hB _ hx hGem hE hJ hQ hD s'; filter_upwards [hX,(hi.program x hp).filter_mono hf] with i hi hf; obtain ⟨r,hr⟩:=hi; exact hr ▸ ((hf v hΓ).2 r|>.2)
end YM.RG05Readout.Aligned
