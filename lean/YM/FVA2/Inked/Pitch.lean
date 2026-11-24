import YM.FVA2.Inked.Orchestra
/-!
# Tree-jet obligation on the actual stencil

`rupture`: here prove `Face` on the generators, for the actual Survey
inputs (at all ranks), by testing against the smooth functions described
in `Hero`, `Synth` etc. See `Inked/TrueF` next: combine these results
into `TreeT.innate` on the Plot. Needed to get the `Teller/Where`
`b=true` rank-budgeted tuning (`Inked/Combined`).
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Inked.Music
open Function Filter Set Finset MeasureTheory Topology
open scoped ContDiff BigOperators Classical
open Lattice RG Maxwell Gen Press Press.Integration
open MS MS.Koszul MS.Plane MS.Native MS.Native.Sew MS.Native.Draft MS.Cylinder MS.Cylinder.Taylor MS.Momentum MS.Theater
open MS.Color MS.Arts MS.Motif MS.Landau MS.Landau.Detect MS.Local.Physical MS.Lifting MS.Halo MS.Book MS.Heat MS.Tone MS.Plane.Wire Source Labels Source.Drops Bid Work XSpace
open Position.OpenAxis
variable {E F J Y : Type}[NormedAddCommGroup E][NormedSpace ℝ E]{G:Gauge}{H:Hol G}{d κ:ℕ}(S:XSpace.Survey G H d)
local notation "P"=> E4
local notation "L"=> Lane4 G
local notation "I"=> Complex.I
local notation "W"=> G.Color
local notation "K"=> Cfield G 0
local notation "T"=> Press.tilt S
local notation "ζ"=> Subtype.val (p:=fun x:Edge Cover=> x∈Press.knots S)
variable {A:Play E G}{Z: E→ Sky G} (h:Hall A Z)(F:Press.tilt S→ℝ)(he:ContDiff ℝ ω F)
local notation "ƛ"=> MS.Cylinder.Taylor.ink
-- cases when some direction is irrelevant
variable {w:Legs (Lane4 G)}
include h
private abbrev Fault (w:Legs (Lane4 G)): Prop:=∃ i∈w,¬Upright i
private lemma doom (hf:Fault w)(f:E→ℝ): ƛ A.shots f w=0:= by obtain ⟨i,hi,hv⟩:=hf; exact ink_uses A.shots ( setOf Upright ) (fun i hv=> h.offL i hv ) f w i hi hv
local notation "ρ"=> ƛ A.shots
-- Use the stated hypotheses on this real test
variable {Y:E→ℝ}{B: Law G}(E₀: Early A Y κ B)
include he E₀
lemma echo (hw:Active A w)(hx:∀ s:E, Near κ (fun t:ℝ=> F (told S Z (s,t))) (fun t:ℝ=> t^κ • Y s) ): Rest ( fieldVal (Tone.run ( Sew.art ζ F )) (ray w) ) (κ-fieldDim wfield w) ( B w ) := by
    obtain hf | hf:= em (Fault w)
    · have he': B w=0:= ( E₀.starts w hw ).symm.trans (by rw [doom h hf,mul_zero])
      refine ⟨ ( site S F w ).complex,fun _=> he',fun j hj=>?_⟩; change torch j _ w=_; rw [ balcony S h F he.contDiffAt j w hw, he' ]; simp_rw [doom h hf]; simp [Plane.reading]
    have hl: fieldDim wfield w=w.length:= whence w (fun i hi=> Classical.byContradiction fun hh=>hf ⟨i,hi,hh⟩); rw [hl]; refine ⟨ ( site S F w ).complex, fun z=> E₀.cap w (by omega), fun j hj=>?_⟩; change torch j ( Tone.run (Sew.art ζ F) ) w=_; rw [ balcony S h F he.contDiffAt j w hw ]; let X(w:E×ℝ):= F ( told S Z w ); let k:=j+w.length; change I^j * MS.Plane.reading k (fun t:ℝ=> ρ (fun x:E=> X (x,t)) w )=_; unfold MS.Plane.reading; have ht(s:E): iteratedDeriv k (fun t:ℝ=> X (s,t)) 0=if k=κ then (k.factorial:ℝ) • Y s else 0:= (hx s k (by unfold k; omega)).trans (lift_symbol ..);
    rw [ ink_t A.shots (f:=X) (he.comp (comfort S h)) ]; simp_rw [ht]; split
    next H=> have hi:(j:ℤ)=(κ-(w.length:ℤ):ℤ):=(by dsimp only [k] at H; omega); rw [if_pos hi]; change I^j*((k.factorial:ℝ)⁻¹ • ƛ _ ( (k.factorial:ℝ) • Y ) w)=_; rw [ink_smul A.shots E₀.smooth.contDiffAt (k.factorial:ℝ) ]; change I^j*( (k.factorial:ℝ)⁻¹ • (( k.factorial:ℝ ) • ρ Y w))=_; rw [ inv_smul_smul₀ (by positivity), ← E₀.starts w hw ]; congr 1; rw [ show (κ-( w.length:ℤ ):ℤ)=j from (by omega), zpow_natCast ]
    next H=> rw [if_neg (by dsimp only [k] at H; omega : (j:ℤ)≠κ-w.length)]; change I^j*(( k.factorial:ℝ )⁻¹ • ƛ _ (0:E→ℝ) w)=_; rw [ink_zero]; simp
omit h he E₀
private lemma channel_key (j:Key G)(hl:j.1 < d-1) (x:Snap G d): channel j x= SP j ( x ⟨j.1,hl⟩ ):= by
    change ( Labels.coord ( expand d x ) j ).re=_; unfold Labels.coord; rw [ expand,dif_pos hl ]; rfl
-- Use the `Survey` hypotheses below
variable (j:Labels.Key G)(hh:j.1<d-1)
include hh
theorem rupture : Face wfield (Tone.run (sat S (MvPolynomial.X j))) ( seed G (MvPolynomial.X j) 1 0 ) (j.1+2:ℤ) false:= by
    intro l hL; rw [sat_X, seed_x ]; obtain ⟨A,hA,h',X,Z,H,W'⟩:= Hall.enough (G:=G) l; have hz(a:A): Fluid ( Z a ):= fun i=> by apply ContDiff.of_le _ (m:=∞) le_top; exact (H.speaks i).comp (f:=fun t:E4=>(a,t)) ( contDiff_const.prodMk contDiff_id );
    choose J hJ using fun x=>origin (hz x); obtain hv:= sky_early H hJ j.1 ( SP j ); obtain e : Early X (fun x:A=> SP j (J x j.1)) ((j.1+2:ℕ):ℤ) ((Ramp G j.1 ( pick j ) 1 0)):=(by rw [Nat.cast_add,Nat.cast_ofNat]; exact hv);
    have he:= echo (κ:=j.1+2) S H (box S j) (Integration.hot S j) e W'; refine ?_ ; -- actually apply with simpa cast.
    have hc:∀ x:A, Near (j.1+2) (fun t:ℝ=> box S j (told S Z (x,t)) ) (minZ (SP j) (J x)):= by
       intro x; -- morning
       let k: Fin (d-1):= ⟨j.1,hh⟩; obtain hr:= morning (hz x) S (hJ x) k ( SP j ); change Near (j.1+2) _ (minZ (SP j) (J x)); rw [ show (fun t:ℝ=> box S j (told S Z (x,t)))=( fun t:ℝ=> SP j ( S.reading (phaseQ ( Z x ) t ) k ) ) from funext (?_ : ∀ t:ℝ,_=_) ]; exact hr; intro t; rw [Integration.box,channel_key j hh,calls]
    simpa only [Nat.cast_add,Nat.cast_ofNat,mounted] using ( he hc )
end YM.FVA2.Inked.Music
