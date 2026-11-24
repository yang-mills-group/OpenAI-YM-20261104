import YM.SchemeConversionRG11.FirstW.Lien.Frame
import YM.SchemeConversionRG11.FirstW.Lien.Regular
/-! Solving over linear maps that are legitimate field/operator increments. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD RawLabels MvPolynomial Position SchemeConversionRG11 SchemeConversionRG11.Horizon
open scoped BigOperators Classical
variable {G : Gauge}
def ColorS (u : G.El) (m : ℕ) (x:Nu G m): Nu G m:=⟨putting u x.val,preserving_color _ _ x.property⟩
def rex (u:Signed)(m:ℕ)(x:Nu G m): Nu G m:=⟨Bare.wideLink G u x.val,track_cabin _ _ x.property⟩
abbrev rink (s:Signed)(x:la G):= rex s 4 x
lemma rex_one (x:Field4 G): Bare.wideLink G 1 x=x:=by funext l; simp [Bare.wideLink_apply,Signed.act_one,Step.rotate_one,posDir,Step.used]
variable (F : Labels.Frames G)
abbrev Letter (G : Gauge) (F:Labels.Frames G) := Position.E F 6→ₗ[ℂ] Rhythm G
structure TintD (A : Letter G F) : Prop where
 lower (p:E F 6): sink p → A p=0
 fair (p:E F 6)(x y:la G): A p x y=A p y x
 color (u : G.El)(p:E F 6)(x y:la G): A p (ColorS u 4 x) (ColorS u 4 y)=A p x y
 realP (p:E F 6)(x y:la G): A (bar F 6 p) x y=star (A p x y)
 rotP(s:Signed)(p:E F 6)(x y: la G): A (tripS F s p) x y = A p (rink s x) (rink s y)
def bath (F : Labels.Frames G) : Submodule ℝ (Letter G F) where
 carrier:=setOf (TintD F)
 add_mem' {a b} ha hb:=by
    change TintD F (a+b)
    change TintD F a at ha; change TintD F b at hb
    refine ⟨fun p hp=>?_,fun p x y=>?_,fun u p x y=>?_,fun p x y=>?_,fun s p x y=>?_⟩
    all_goals first | rw [LinearMap.add_apply,ha.lower _ hp,hb.lower _ hp, add_zero] | exact congrArg₂ (·+·) (ha.fair p x y) (hb.fair p x y) | exact congrArg₂ (·+·) (ha.color u p x y) (hb.color u p x y) | exact congrArg₂ (·+·) (ha.rotP s p x y) (hb.rotP s p x y) | simp only [LinearMap.add_apply,ha.realP,hb.realP,star_add]
 smul_mem' r p hp:=by
    change TintD F p at hp; change TintD F (r • p)
    refine ⟨fun w h=>?_,fun w x y=>?_,fun u w x y=>?_,fun w x y=>?_,fun s w x y=>?_⟩
    · rw [LinearMap.smul_apply,hp.lower w h,smul_zero]
    · exact congrArg (r • ·) (hp.fair w x y)
    · exact congrArg (r • ·) (hp.color u w x y)
    · simp only [LinearMap.smul_apply,hp.realP, star_smul,star_trivial]
    exact congrArg (r • ·) (hp.rotP s w x y)
 zero_mem':=⟨fun _ _=>rfl, fun _ _ _=>rfl,fun _ _ _ _=>rfl,fun _ _ _=> star_zero _ |>.symm,fun _ _ _ _=>rfl⟩
abbrev Bond (F : Labels.Frames G):= ↥(bath F)
variable {F} {k : ℕ}
def cloth (G: Gauge): Paper G→ₗ[ℂ] Reel G:= Submodule.inclusion (show smock G ≤ Reel G from inf_le_left)
lemma worn (v:Paper G): (cloth G v).val=v.val:=rfl
lemma tab_cloth (p : Reel G) : ∃ v: Paper G,∀ B: Reel G →ₗ[ℂ] ℂ,B (cloth G v)=∫ t:G.El,B (colorsP t p) ∂G.probHaar := by
 obtain ⟨v,H⟩:= tabulated p
 refine ⟨v,fun B=>?_⟩
 rw [show cloth G v=⟨v.val,(show v.val∈Reel G from (Submodule.mem_inf.mp (show v.val∈ Reel G ⊓ Labels.invariantSpace G from v.property)).1)⟩ from Subtype.ext rfl]; exact H B
lemma ridesH {p:Rhythm G} {u:G.El} (hE:∀ x y:la G,p (ColorS u 4 x) (ColorS u 4 y)= p x y) (r: Reel G) (hs:ripple _ p r k) : ripple _ p (colorsP u r) k:= by
 intro i j hij x y hx hy
 rw [testedColor,←hE x y]; let a:=ColorS u 4 x; let b:=ColorS u 4 y
 have he (x:la G) : putting u x.val=(ColorS u 4 x).val:=rfl
 rw [he,he]; have h1 : a.val∈cabin G i:=by unfold a; rw [←he]; exact preserving_color u _ hx
 have h2 : b.val∈cabin G j:=by unfold b; rw [←he]; exact preserving_color u _ hy
 have hl:= hs i j hij (ColorS u 4 x) (ColorS u 4 y) h1 h2; exact hl
lemma paintUp (G : Gauge) (A B:la G) (r:Reel G)(q:Paper G) {c:ℂ} (h:∀ v:G.El, chord A.val B.val (colorsP v r).val=c) (hp:∀ F: Reel G→ₗ[ℂ]ℂ,F (cloth G q)=∫ t:G.El,F (colorsP t r) ∂G.probHaar) :
 chord A.val B.val (cloth G q).val=c := by
 let e:= (chord A.val B.val).comp (Reel G).subtype
 rw [show chord A.val B.val (cloth G q).val=e (cloth G q) from rfl,hp e]; simp only [e, LinearMap.comp_apply, Submodule.subtype_apply,h]; simp
lemma pocket (p : Rhythm G) (hp:ToneR p k) (hk:k≤4)(hr : pastR p k)
    (hE:∀ u:G.El,∀ x y:la G,p (ColorS u 4 x) (ColorS u 4 y) = p x y) : ∃ q:Paper G,ripple G p (cloth G q) k := by
  obtain ⟨r,hs⟩:= togetherR p hk hp hr; obtain ⟨q,H⟩:=tab_cloth r
  exact ⟨q,fun i j hij x y hx hy=> (paintUp G x y r q (fun v=>(ridesH (hE v) r hs i j hij x y hx hy).symm) H).symm⟩
abbrev PlayerM (F:Labels.Frames G) := Module.End ℂ (E F 6)
def CompR (W:Bond F) (n : ℕ) (B:PlayerM F) : Prop:= ∀p:E F 6,∀ i j:ℕ,i+j ≤ n → ∀ x y:la G,x.val∈cabin G i → y.val∈cabin G j → chord x.val y.val (Full.sections 6 F (B p)) = W.val p x y
-- build arbitrary global increments using one linear inverse, then impose star+spin exactly.
def Quieten (F:Labels.Frames G) (n:ℕ) (W:Bond F) := ∀p, ToneR (W.val p) n ∧ pastR (W.val p) n
lemma ontoQ (F : Labels.Frames G) (W:Bond F)(n : ℕ) (hn:n≤4) (hq:Quieten F n W): ∃ B:PlayerM F,(∀ p:E F 6,B p∈ Hex F) ∧ (∀ p:E F 6,sink p → B p=0) ∧ CompR W n B:= by
  let X := { x:(ℕ×ℕ)× (la G × la G)//x.1.1 + x.1.2≤n ∧ x.2.1.val∈cabin G x.1.1 ∧ x.2.2.val∈cabin G x.1.2}
  let L : Hex F→ₗ[ℂ] (X→ℂ) := LinearMap.pi fun x=> chord x.val.2.1.val x.val.2.2.val ∘ₗ (Full.sections 6 F ∘ₗ (Hex F).subtype)
  let A : E F 6 →ₗ[ℂ] (X→ℂ):= {
    toFun p x:= W.val p x.val.2.1 x.val.2.2
    map_add' p q:=by ext1 x; simp
    map_smul' c p:=by ext1 x; simp }
  have hp(p:E F 6): A p∈ L.range:=by
    obtain ⟨q,H⟩:= pocket (W.val p) (hq p).1 hn (hq p).2 (fun u x y=> (show TintD F W.val from W.property).color u p x y)
    let y:=sendP F q
    let Y:Hex F:=⟨y,show Full.sections 6 F y∈Reel G from send_ref F q|>.symm ▸ q.property.1⟩
    refine ⟨Y,funext fun x=>?_⟩
    change chord x.val.2.1.val x.val.2.2.val (Full.sections _ _ y)=W.val p x.val.2.1 x.val.2.2
    unfold y; rw [send_ref]; rw [←worn]; exact (H _ _ x.property.1 _ _ x.property.2.1 x.property.2.2).symm
  obtain ⟨Q,H⟩:= choosingR L
  refine ⟨(Hex F).subtype.comp (Q.comp A),fun p=> (Q (A p)).property,fun p hP=>?_,fun p i j hij x y hx hy=>?_⟩
  · have he : A p=0:=funext fun x=>by change W.val p x.val.2.1 x.val.2.2=0; rw [(show TintD F W.val from W.property).lower p hP];rfl
    simp only [LinearMap.comp_apply,he,map_zero]
  have he : L (Q (A p))=A p:=by obtain ⟨z,hz⟩:=hp p; rw [←hz,H]
  have heV:=congrFun he (⟨⟨⟨i,j⟩,x,y⟩,hij,hx,hy⟩: X); dsimp only [A,LinearMap.comp_apply,LinearMap.coe_mk,AddHom.coe_mk,L,LinearMap.pi_apply, Submodule.subtype_apply] at heV ⊢; exact heV
end YM.RG11.FirstW
