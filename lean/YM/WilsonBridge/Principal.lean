import YM.WilsonBridge.MidShip
/-!
# The free radial operator dictionary (leading jet projection)

Highest rank ONLY of each mark through a weight; this is the `Fit` required
by the MS operator label. Proved for the shared actual top bare Wilson stencils,
working before position frame. Includes λ(t,w)-proof on arbitrary momentum legs.
No perfect derivative assumption behind the rank reconstruction, and `Projects`
keeps its full holonomy convention. Includes frame labels even those with
lower own horizon.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonBridge.Glyphs
open Reader Function Finset Filter Set Sailing Wisdom
open PertExtension PositionX Next.Rank
open MS Book Koszul Cylinder Lab Native Native.Studio Sew MS.Theater
open Plane Native.Chart Tone Tone.Frame Landau Detect Wire
open scoped ContDiff Topology BigOperators RealInnerProductSpace
open InnerProductSpace Momentum Lattice LatticePT
open MvPolynomial
open Complex (I)
variable {G:Gauge}{N:Type} {d i j:ℕ}
local notation "Χ"=> Draft.DotFlip (G:=G) (P:= QP)
local notation "Ψ"=> MS.Theater.orbit G
-- reader linear: derivative sums all characters of p at phase. Ranks unbounded.
def remit : Stems.Curly G→ₗ[ℂ] Law G:= Tone.run ∘ₗ tattoo G
variable (w:W G)
def share (w:W G) (j:ℕ): Stems.Curly G→ₗ[ℂ] ℂ where
    toFun u:= reading j (pose takeW w (remit u))
    map_add' x y:= by
       let f (p: Stems.Curly G):= fieldVal (remit p) (ray w); rw [map_add,map_add]; have he p : ContDiff ℝ ∞ (pose takeW w (remit p)):= by
            rw [funext (fun t=>posing takeW w t (remit p))]; apply ContDiff.mul (Complex.ofRealCLM.contDiff.pow _); exact (extra_s ells w).mul (Menus.all_smooth ..)
       exact read_add (he x) (he y)
    map_smul' c x:= by rw [ map_smul,map_smul]; exact read_const ..
def duty (w:W G)(j:ℕ): Labels.Pol G→ₗ[ℂ] ℂ := LinearMap.proj w ∘ₗ MS.Theater.orbit G ∘ₗ Next.Foundations.tier j
lemma dutiful (u:Labels.Pol G) (j:ℕ) : duty w j u=reading j (base w (Ψ u)):= ( skill u j w ).symm
lemma duty_page (L: Witness G i): duty w j (page i L)= if i+2=j then Koszul.mono ( RowLeg G i L ) w else 0:= by
    rw [dutiful, funext ( fun t=> hold ( formA (bypage L) ) w t ),power_j,pageX ]; -- notation ζ undefined
omit w in
lemma remainX (v:Stems.Hair G): remit (X v)= Koszul.mono fun i:Lane4 G=> paywave i (port v) := by
    change run (tattoo G _)=_; rw [tattoo_X]; funext w; rcases w with _|⟨x,_|v⟩; simp [run,Cylinder.single, atLetter,mono]; exact Tone.pulse ..; rw [D_eval _ (run _), run, names]; simp [mono,coin] -- rank_layout
-- compact Sc concat
lemma free_s (v:Stems.Curly G): ContDiff ℝ ∞ (Reader.pose takeW w (remit v)):= by rw [funext (fun t=>posing takeW w t (remit v))]; exact (Complex.ofRealCLM.contDiff.pow _).mul ((extra_s ells w).mul (Menus.all_smooth ..))
omit w in
lemma on_X (i:ℕ)(p:QP)(a:Axis)(c:Conn G)(v:Stems.Hair G):
     share [ waveForm p a c ] (i+1) (X v)= hitϑ i* (↑( trip i v.1 ( speak i a p (cl G c) ) v.2):ℂ) := by
    rcases v with ⟨⟨x,b⟩,k⟩; let V:Stems.Hair G:= ((x,b),k); let j:=waveForm p a c; let f(t:ℝ):= takeW j t * paywave (waveForm (t • p) a c) (formAt b k x)
    have ht: pose takeW [j] (remit (X V))=(fun t:ℝ=>(t:ℂ)^1 * f t):= by
        funext t; rw [posing, remainX V]; simp only [fieldVal,ray_go,List.map_cons,List.map_nil, extras, List.prod_cons, List.prod_nil, mul_one ]; rfl
    change reading (i+1) _=_; rw [ht, tpay, if_pos (by omega),Nat.add_sub_cancel]; exact test_result ..
    unfold f; simp_rw [show ∀ t:ℝ,takeW j t * paywave _ _= _ from fun t=>edge_test x p a b c k t]; by_cases ha:(a=b ∧ c=k); simp_rw [if_pos ha]; exact wholeS ..; simp_rw [if_neg ha]; exact contDiff_const
omit w in
lemma on_0 (p:QP)(a:Axis)(c:Conn G)(v:Stems.Hair G): share [waveForm p a c] 0 (X v)=0:= by rw [share]; change reading 0 _=_; simp only [reading, Nat.factorial_zero,Nat.cast_one,inv_one,iteratedDeriv_zero,one_smul]; rw [posing,show extent [waveForm p a c]=1 from rfl]; simp
-- infer by cases on row, OFF λ analytic direct. helpers
private def liveA (w:W G) := ∃ (p:QP)(a:Axis)(c:Conn G),w=[ waveForm p a c ]
private lemma unpaid (x:Stems.Hair G)(h:¬liveA w): fieldVal (remit (X x)) (ray w)=0:= by
    rw [remainX]; funext y; rw [fieldVal,ray_go]; rcases w with _|⟨ ⟨ ⟨⟨_|i,b⟩,t⟩,p⟩,_|v⟩ <;> first| rfl| skip
    · apply Classical.byContradiction fun h'=>?_ ; obtain hx:= in_light (v:= (((none,b),t),y • p) ) (x:=port x) h'; cases hx
    cases b; exact False.elim (h ⟨p,i,t,rfl⟩); apply Classical.byContradiction fun h'=>?_ ; obtain hx:= in_light (v:= (((some i,true),t),y • p) ) (x:=port x) h'; cases hx
private lemma unpage (L:Witness G i) (h:¬liveA w): Koszul.mono ( RowLeg G i L ) w=0:= by
    rcases w with _|⟨ ⟨⟨⟨_|i,b⟩,t⟩,p⟩, _|v⟩ <;> first| rfl|skip
    cases b; exact False.elim (h ⟨p,i,t,rfl⟩); rfl
private lemma arc_v (v:LatticePT.Atom G):
       let i:=v.1.plaq.val.1; let j:=v.1.plaq.val.2; let x:=v.1.offset; let k:=v.2
       Stems.loom (X v)= X ((x,i),k)+ X ((x+step i,j),k)-X ((x,j),k)-X ((x+step j,i),k):= by
    intro i j x k; rw [Stems.loom, Normal.exchange_x, Function.comp_apply,Stems.com_text, Stems.blade, Stems.iris,Stems.arc]; simp_rw [_root_.map_sub,_root_.map_add,Finsupp.linearCombination_single,one_smul]
    rfl
lemma label_out (u:LatticePT.Atom G)(j d:ℕ)(hd:j≤d): share w j (Stems.loom (X u))= duty w j ( Heat.Ray.print d (X u) ):= by
    let a:=u.1.plaq.val.1; let b:=u.1.plaq.val.2; let x:=u.1.offset
    let V (i:ℕ):Witness G i:= Complex.ofRealCLM.toLinearMap ∘ₗ LinearMap.proj (Heat.Ray.address u) ∘ₗ Beamer.sweep i
    rw [arc_v u, print_L d u]; simp_rw [map_sum,map_sub,map_add,duty_page]
    by_cases hv: liveA w; swap
    · have h0(t:Stems.Hair G): share w j (X t)=0:= by change reading j _=_; rw [show pose takeW w (remit (X t))=0 from (by ext1 y; rw [posing,unpaid w t hv]; simp)]; simp [reading]
      simp_rw [h0, add_zero,sub_zero,unpage w _ hv,ite_self]; simp
    obtain ⟨p,i,c,rfl⟩:=hv; cases j; · simp_rw [on_0]; simp
    rename_i j; simp_rw [on_X];
    have he (j:ℕ) : hitϑ j * (↑((trip j (x,a)) (speak j i p (cl G c)) u.2):ℂ) + hitϑ j * ( ↑((trip j (x+step a,b)) (speak j i p (cl G c)) u.2):ℂ)- hitϑ j * ( ↑((trip j (x,b)) (speak j i p (cl G c)) u.2):ℂ) - hitϑ j * ( ↑((trip j (x+step b,a)) (speak j i p (cl G c)) u.2):ℂ)= hitϑ j * ↑( cycle x a b j (speak j i p (cl G c)) u.2):= by unfold Sailing.cycle; simp only [LinearMap.sub_apply,LinearMap.add_apply,PiLp.sub_apply,PiLp.add_apply]; push_cast; ring
    rw [ he ]; cases j; · rw [cycle₀]; simp only [PiLp.zero_apply,Complex.ofReal_zero,mul_zero]; rw [Finset.sum_eq_zero]; intro i hi; rw [if_neg (by omega)]
    rename_i j; rw [ Finset.sum_eq_single_of_mem j ( Finset.mem_range.mpr (by omega) ),if_pos rfl, retrip ]; rfl
    intro v hv hu; exact if_neg (by omega)
omit w in
theorem radius (P: Normal.poly (LatticePT.Atom G))(d:ℕ) : Adjoin takeW (run (tattoo G (Stems.loom P))) (Ψ (Heat.Ray.print d P)) d:= by
    induction P using MvPolynomial.induction_on with
    | C x=> rw [ show Stems.loom (G:=G) (MvPolynomial.C x)=MvPolynomial.C x from Stems.loom.commutes x, show Heat.Ray.print d (MvPolynomial.C x)=MvPolynomial.C x from (Heat.Ray.print d).commutes x, tattoo_C, cus ]; unfold Tone.run; rw [coin_turn]; exact Adjoin.coinA x
    | add p q hp hq=> simp_rw [map_add]; exact hp.sum hq
    | mul_X p i hp=> rw [ map_mul, map_mul (Heat.Ray.print d), tattoo_M,Tone.wave_cost,bags]; exact hp.pair (fun w=> ⟨free_s w _,orbit_s ..,fun j hj=> (label_out w i j d hj).trans (dutiful w (Heat.Ray.print d (X i)) j)⟩)
omit w
section MC
open Source Heat.Top Vertex
-- pure birth jets for *any* label, at declared grading.
variable {W: Labels.Frame G d}{S: SectionData W}{H:Hol G}
theorem brightK (i: W.Index)(h:S.Sound H)(P: Bid.pop S):
       Lifting.Fits ( coreK h P i ) ( Ψ ( W.basis i ).val ) (W.grades i).2 ( W.grades i ).1 false := by
    let R:=(topMatrix S H h P).basis i; have hz : model (↑(W.grades i).2) ( coreK h P i )= tattoo G ( Stems.loom R ):= by rw [Stems.basis_moon,coreK,glyph_K];
    have he := ( radius R d ); have hx : Heat.Ray.clipped d R=(W.basis i).val:= by
       obtain ht:= (topMatrix S H h P).retr i; change joint W R=_ at ht
       have hp:=Heat.HueTag.shadow_eq (F:=W) R (basis_fixed S H h P i); rw [ht,← W.coords_basis,LinearEquiv.symm_apply_apply] at hp; exact congr_arg Subtype.val hp.symm
    have hv:= Adjoin.trunc takeW he; rw [show Next.Foundations.capRead d _=(W.basis i).val from hx] at hv; -- ↑cast syntax
    unfold Lifting.Fits; rw [← Tone.grade,hz]; refine Adjoin.cancels (fun w=> ⟨(hv w).left,(hv w).right, fun j hj=> (hv w).char j (hj.trans (W.bound i))⟩) ells ell1 (formA (( Labels.pure_grade _ _ ).mp ( W.pure i ))) -- pure_grade orientation & `glyph_K`
end MC
end YM.WilsonBridge.Glyphs
