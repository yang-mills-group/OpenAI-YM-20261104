import YM.RegulatorIR.Older.Adjacent

/-!
# Agreement of conditional rules on period forks

Independent cover-positive operations on overlapping ages. Lifts all W1
lore may vary by period; if matched on overlap, cover reports ignore orbital
coefficient data. Required for UV diagonal proof. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Older
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Sources Centered Capture Labels Source
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W W' I U: Type}{q u b p a i j e k d m r s:ℕ}{M: W→ℕ}{M': W'→ℕ}{n:Page M→Side}{n':Page M'→Side}{L:Meter W}
variable {S:Heir n G}(R: Reel S){S':Heir n' G}(R': Reel S')
variable (T:S.Accounts)(T': S'.Accounts)
variable {c f c' f': Side}

private def trimSteps (S:StepData c f):StepData 1 S.patch.L:= ⟨S.patch,S.kernel,by rw [PNat.val_ofNat];omega⟩
private lemma stepsExt (K P:StepData c f)(h:K.patch=P.patch)(hh:K.kernel=P.kernel): K=P:=by cases K;cases P;simp only [StepData.mk.injEq];exact ⟨h,hh⟩
private lemma films (v c f c' f': Side) (K : StepData c f) (P:StepData c' f')(h:c'=v*c)(hh:f'=v*f)(hp:P.patch=K.patch)(hG:P.kernel=K.kernel) (S:Scale) : prism (G:=G) P (bios P) S=prism K (bios K) S:=by
 subst c'; subst f'; have he: P=climbS K v:= stepsExt _ _ hp hG
 rw [he, axi]
private lemma trims (S:StepData c f)(L:Scale) : prism (G:=G) S (bios S) L=prism (trimSteps S) (bios (trimSteps S)) L:=films c 1 _ c f (trimSteps S) S (mul_one _).symm (Subtype.ext S.sizes) rfl rfl L
lemma neverP (S:StepData c f)(S':StepData c' f') (H:S.patch=S'.patch)(h:S.kernel=S'.kernel)(t:Scale) : prism (G:=G) S (bios S) t=prism S' (bios S') t:=by
 rw [trims S,trims S']
 cases S with | mk P k z => cases S' with | mk A v y =>
    dsimp only at H h; subst A; subst k; rfl

-- uniform bookkeeping, aged prefix with additional optional capacities elsewhere
variable (w: W)(w':W')(j:Choice M)(i:Choice M')
def briefly (j : Choice M) (w : W) (u : ℕ)(h:u≤j.age w): Page M:=⟨w,u,h.trans (j.young w)⟩
def wingS (j : Choice M)(w:W)(u:ℕ)(h:u<j.age w): Flap M:= ⟨w,u,h.trans_le (j.young w)⟩
structure Overlap (R:Reel S)(R':Reel S')(w:W)(w':W')(j:Choice M)(i:Choice M'): Prop where
 atJ : j.age w=i.age w'
 birth : S.ε w=S'.ε w'
 wages u h hh:R.clock (briefly j w u h)=R'.clock (briefly i w' u hh)
 patch u h hh : (R.steps (wingS j w u h)).patch=(R'.steps (wingS i w' u hh)).patch
 kernel u h hh : (R.steps (wingS j w u h)).kernel=(R'.steps (wingS i w' u hh)).kernel
 mean u h hh:R.Dtr (wingS j w u h)=R'.Dtr (wingS i w' u hh)
 cov u h hh: R.pulses (wingS j w u h)=R'.pulses (wingS i w' u hh)

variable {R R' w w' j i}(h : Halo.Common R)(H: R.Follows T)(h' : Halo.Common R')(H': R'.Follows T') (K:Overlap R R' w w' j i)
include K
lemma overlap_l {u:ℕ} (hv:u  ≤ j.age w)(he:u ≤ i.age w') : S.l (briefly j w u hv)= S'.l (briefly i w' u he):=by
 induction u with
 | zero=> exact K.birth
 | succ u ih=>
    let x:= wingS j w u hv;let y:= wingS i w' u he;change S.l x.next= S'.l y.next
    rw [scaledCard R,scaledCard R',show S.l x.prev=S'.l y.prev from ih (by omega) (by omega), K.patch u hv he] -- defs

structure Sonic {P Q:ℝ}{X Y U V W B:Type}{A:Deck P X U}{F:Deck P Y V}{C:Deck Q X W}{D:Deck Q Y B}(J:GridStep A F)(K:GridStep C D): Prop where
 addon:J.addon=K.addon
 layers:J.line=K.line
 drifting:J.driftL=K.driftL
namespace Sonic
variable {P Q:ℝ}{X Y U V W B:Type}{A:Deck P X U}{F:Deck P Y V}{C:Deck Q X W}{D:Deck Q Y B}{J:GridStep A F}{B':GridStep C D}(So:Sonic J B')
omit K
include So
lemma joints (T: Orders X): J.jVac T=B'.jVac T:=by ext1 i;ext1 j; unfold GridStep.jVac;rw [So.addon];rfl
lemma pales (T:Orders X): J.pure T=B'.pure T:=by ext1 i;ext1 j; unfold GridStep.pure; rw [So.joints,So.layers]; unfold GridStep.pullI; rw [So.drifting]; rfl
lemma marks (T W:Orders X): J.each m T W=B'.each m T W:=by ext1 i;ext1 j; unfold GridStep.each; rw [So.joints,So.layers]; unfold GridStep.pullI; rw [So.drifting]; rfl
end Sonic
include h h'
lemma sing (u:ℕ)(he:u< j.age w)(hf:u < i.age w'):Sonic (S.frames (wingS j w u he)) (S'.frames (wingS i w' u hf)) :=by
 let x:=wingS j w u he; let y:=wingS i w' u hf
 refine { layers:= by rw [R.bondF,R'.bondF,K.cov], drifting:=by rw [R.meanF,R'.meanF,K.mean], addon:= ?_ }
 obtain ⟨z,hz,H⟩:= R.powers x; obtain ⟨z',hz',H'⟩:= R'.powers y
 have hx:R.clock x.prev=R'.clock y.prev:= K.wages u he.le hf.le;rw [hx] at hz
 have hQ:prism (G:=G) (R.steps x) (R.forest x) (R'.clock y.prev) = prism (R'.steps y) (R'.forest y) (R'.clock y.prev):=by rw [h x,h' y]; exact neverP (R.steps x) (R'.steps y) (K.patch u he hf) (K.kernel u he hf) _
 unfold Sphere at hz; rw [hQ] at hz
 exact H.trans ((congr_arg many (funext (fun i=>(hz i).unique (hz' i)))).trans H'.symm)
include H H'
lemma processes (u:ℕ) (hx:u ≤ j.age w)(hy:u ≤ i.age w'): T.bulk (briefly j w u hx)=T'.bulk (briefly i w' u hy):=by
 induction u with
 | zero=>
    obtain ⟨t,h,hv,h'⟩:=H w; obtain ⟨q,hq,hq',H'⟩:=H' w'; have hz:R.clock (Page.opening M w)=R'.clock (Page.opening M' w'):= K.wages 0 hx hy;rw [hz] at h
    exact hv.trans ((congr_arg many (funext (fun i=>(h i).unique (hq i)))).trans hq'.symm)
 | succ u ih=>
    let x:= wingS j w u hx;let y:=wingS i w' u hy; rw [show briefly j w (u+1) hx=x.next from rfl,show briefly i w' (u+1) hy=y.next from rfl,← T.step_v x,← T'.step_v y, show T.bulk x.prev=T'.bulk y.prev from ih (by omega) (by omega)]
    exact (sing h h' K u hx hy).pales ..
lemma lighting {B:(portraitR T).Report m}{C:(portraitR T').Report m}{x:Room}(U:B.main (Page.opening (signM M) (w,x))= C.main (Page.opening (signM M') (w',x))) : medium S T B j e w x=medium S' T' C i e w' x:=by
 have ht(u:ℕ)(hx:u ≤ j.age w)(hy:u ≤ i.age w') : B.main (leafX (briefly j w u hx) x)=C.main (leafX (briefly i w' u hy) x):=by
    induction u with
    | zero=> exact U
    | succ u ih=>
       let z:= wingS j w u hx;let v:= wingS i w' u hy
       change B.main (turnX z x).next=C.main (turnX v x).next
       calc
        _ = (S.frames z).each m (T.bulk z.prev) (B.main (turnX z x).prev):=(B.step_m _).symm
        _ = (S'.frames v).each m (T'.bulk v.prev) (C.main (turnX v x).prev):= by
            rw [show B.main (turnX z x).prev=C.main (turnX v x).prev from ih (by omega) (by omega),show T.bulk z.prev=T'.bulk v.prev from processes T T' h H h' H' K u (by omega) (by omega)]; exact (sing h h' K u hx hy).marks ..
        _ = _:= C.step_m ..
 let P:= j.choose w; let f:=briefly i w' (j.age w) K.atJ.le
 have hp:B.main ((spool j (film W)).choose (w,x))= C.main (leafX f x):= ht _ le_rfl K.atJ.le
 change note (B.main _ e 0)= _; rw [hp,show f= i.choose w' from ?_]; rfl
 unfold f; rw [show i.choose w'= briefly i w' (i.age w') le_rfl from rfl]; congr! 2; exact K.atJ -- dependent

lemma unionPrice {B:(portraitR T).Report m}{C:(portraitR T').Report m}(U:∀ x:Room,B.main (Page.opening (signM M) (w,x))=C.main (Page.opening (signM M') (w',x))): diffuse S T B j e w= diffuse S' T' C i e w':=by
 let f:=briefly i w' (j.age w) K.atJ.le
 have hx:S.l (j.choose w)= S'.l (i.choose w'):=by
    rw [show i.choose w'= f from ?_]; exact overlap_l K le_rfl K.atJ.le
    rw [show i.choose w'= briefly i w' (i.age w') le_rfl from rfl]; unfold f; congr! 2; exact K.atJ.symm
 unfold diffuse;rw [hx,show medium S T B j e w= medium S' T' C i e w' from funext (fun x=>lighting T T' h H h' H' K (U x) (e:=e))]

section Fields
variable {Hol:Hol G} {d : I→ℕ}{F:∀ i,Labels.Frame G (d i)} (Z:(i:I)→ Fabric R (F i) Hol) (Z' :(i:I)→ Fabric R' (F i) Hol)
variable (Φ :(i:I)→W→PhaseTests (d i))(Ψ:(i:I)→W'→PhaseTests (d i))(J:Composite I)
omit h h' H H' K in
structure RootCoherent : Prop where
 source (kk): J.In kk → (Z kk).A=(Z' kk).A
 accent kk: J.In kk→ (Z kk).accent w=(Z' kk).accent w'
 tap kk : J.In kk→ (Z kk).tap w=(Z' kk).tap w'
 phi kk:J.In kk→ Φ kk w=Ψ kk w'
omit h h' H H' in
lemma twins (E:RootCoherent (w:=w ) (w':=w') Z Z' Φ Ψ J) (x:Room): (principal J (Stall R Z Φ T)).main (Page.opening (signM M) (w,x))=(principal J (Stall R' Z' Ψ T')).main (Page.opening (signM M') (w',x)):=by
 let s (α:I):= (Z α).drawnU w x (Φ α w); let p(α:I):=(Z' α).drawnU w' x (Ψ α w'); have H(i)(hi:J.In i) : s i=p i:= by
    let V:= (Z i).readB w x (Φ i w);have hP :V= (Z' i).readB w' x (Ψ i w'):=by unfold V Fabric.readB; rw [E.phi i hi, E.source i hi,E.accent i hi,E.tap i hi,K.birth]
    have hz := (Z i).depicts w x (Φ i w); have hx:= (Z' i).depicts w' x (Ψ i w')
    exact certifies (hP ▸ (show _ from hz.1)) hx.1 hz.2 hx.2
 exact comb J H
where
 comb (J: Composite I) (H:∀ i, J.In i → (Z i).drawnU w x (Φ i w)= (Z' i).drawnU w' x (Ψ i w')) : J.product (fun i=> (Z i).drawnU w x (Φ i w))=J.product (fun i=>(Z' i).drawnU w' x (Ψ i w')):=by
    induction J with
    | atom i=> exact H i rfl
    | pair P Q ih ih'=> exact congr_arg₂ accord (ih (fun i hi=> H i (Or.inl hi))) (ih' (fun i hi=> H i (Or.inr hi)))
end Fields
end YM.RegulatorIR.Older
