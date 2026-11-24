import YM.FVAAlt2.Mass.Vanishing
/-!
# The finite (all orders compatible) rotation.Mass
Alternative method of determining N. Characterize it by its **necessary** two-sided mass-independent separated-correlation bound (+ real orientation/H-compatibility and strictly-lowering increments). Existence and uniqueness *exactly*,
 using Gram tangent frozen and power separation. This avoids extra RG/reparameterization
 assumptions / β equations. Subsequent characterization relative to the
 `Rails/Street` determination (if given flow on those stronger hypotheses). In particular
 we do not assume Z is grade-preserving as a premise. N depends only on the
 **position WilsonX prescription** (even though existence proved by applying the MS continuum theorem). No comparison to Legend (uses different filter). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Mass
open Function Finset Filter MeasureTheory Topology Set Metric
open Labels Precision Extra.FD Maxwell Extraction FormalOPE FormalOPE.RG10 RG10.Position.Grade
open PertExtension PertExtension.LatticePT PertExtension.Position PertExtension.Position.Triangle RG10.Position RG10.Gazebo RG10.Carryon RG10.InversionTop
open MS MS.Koszul MS.Menus MS.Book MS.Local.Physical MS.Land MS.FVA.Currency
open PowerSeries (C coeff constantCoeff)
open Home Home.Report Matrix Home.Profiles Convert Next.UVStress
open Real
open scoped Topology BigOperators PowerSeries ContDiff Classical Matrix
variable {G:Gauge}{F:Frames G}{d k m n:ℕ}
local notation:max "V_" d:max=> RG10.Position.Deck F d
local notation "ζ"=> Deck.price F d
local notation "V"=> RG10.Position.Deck F d
local notation "FW" => Matrix V V fps
local notation:max "Mk" d:max=> Matrix (RG10.Position.Deck F d) (RG10.Position.Deck F d) fps
local notation "Ω"=> constantCoeff (R:=ℝ)
private lemma reverse_cancel {X A B:Matrix (RG10.Position.Deck F d) (RG10.Position.Deck F d) fps}(hx: Weight X) (h: A*X=B*X): A=B:=by
 obtain ht:= congr_arg (fun v: FW=> v*X⁻¹ ) h; change A*X*_ = _ at ht; simp_rw [ Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hx.det,Matrix.mul_one ] at ht; exact ht
variable {P:Plan F}{U: Booked (Home.seats P.liftOff P.certified)}{W:Drivers} 
structure MassCost (F:Frames G)(g:Datum (RG10.Position.Deck F d)→fps)(N:Matrix (RG10.Position.Deck F d) (RG10.Position.Deck F d) fps) : Prop where
 sober : Weight N -- zero & Upright real&kills unit
 ticket : tile ( Deck.price F d ) N=1 -- stronger than Cut; exactly N=I+positive-order strictly grade-lowering
 revenue : EvenCost ( Deck.price F d ) (mix g N) -- membership on continuum data of the X *position* scheme
-- arranged as suggested `N=tile Zpre * Zpre^-1`. Since inputs act on row.
variable (P) (Y: Patience P W) (Q:ChartRatio G)(hP:P.liftOff=LoftPP F)(hq:LocalRatio Q)(hg:G.Simple)
variable (μ:ℝ) (S:MS.Land.MS_Data G U)
variable {X:Prescription ( Home.seats P.liftOff P.certified )}(H: Launch (Lobby.Table (nativeR P) (seats P.liftOff P.certified)) S (F:=F) X)
local notation:max "R_" n:max=> science μ S F n
local notation "L"=> Zpre P μ S d
local notation "f'"=> f P μ S
-- event.Yields ANY transfer system Patience, hence uniquely independent of actual limits
include Y
lemma pre_weight : Weight L:= ⟨ Z_head μ P S Y.certified, Z_tilt μ P S Y.certified⟩
omit Y
abbrev ζfinal(d:ℕ) : Mk d:= tile ( Deck.price F d ) ( Zpre P μ S d )
private abbrev goal(d:ℕ): Mk d:= ζfinal P μ S d*( Zpre P μ S d )⁻¹
local notation "T"=> goal P μ S d
structure Framed (C:Patience P W)(Z:∀ i:ℕ,Matrix ( RG10.Position.Deck F i ) ( RG10.Position.Deck F i ) fps) : Prop where
 born (d:ℕ) : MassCost F (C.Yield (d:=d)) (Z d)
 tower {d k:ℕ} (h:d≤k): (Z k).submatrix (Deck.climb F h) (Deck.climb F h)=Z d
include Y
lemma paidZX : Weight (goal P μ S d) ∧ Weight (ζfinal P μ S d):=by have he:Weight ( Zpre P μ S d ):= pre_weight P Y μ S; exact ⟨ he.tiled.mult he.invert,he.tiled⟩
lemma pricing : (T)*L=ζfinal P μ S d:= by unfold goal; rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul L (pre_weight P Y μ S|>.det),mul_one]
include H hg hq hP
lemma bona : MassCost F (Y.Yield (d:=d)) T:=by
 obtain hp:Weight L:= pre_weight P Y μ S; have hz:= paidZX P Y μ S (d:=d); refine ⟨hz.1,?_,?_⟩; rotate_left
 · have hh:= price_Gx (Q:=Q) P hP hq X μ S hg Y.certified H Y (d:=d); rw [ hh,mix2,pricing ( Y:=Y ) ]; exact ( science_cost (F:=F) S μ hq (nativeR P) hg ).coastal f'|>.tilted tile_layer
 unfold goal ζfinal; rw [ Cut.tile hz.2.off_bill hp.invert.off_bill ]; rw [ layer_fixed (tile_layer) ]; rw [ ← Cut.tile hp.off_bill hp.invert.off_bill, Matrix.mul_nonsing_inv _ hp.det, layer_fixed (tiled_one ζ) ]
lemma necessary {A:Matrix (Deck F d) (Deck F d) fps}(h:MassCost F (Y.Yield (d:=d)) A): A* ( Zpre P μ S d )= ζfinal P μ S d:=by
 let p:= (f').charge ∘ science μ S F d; obtain hX: Weight L:= pre_weight P Y μ S; have hc : EvenCost ζ p:= ( science_cost ( F:=F ) S μ hq (nativeR P) hg ).coastal f'
 have ht:= h.revenue; rw [ price_Gx P hP hq X μ S hg Y.certified H Y, mix2 ] at ht
 have hw : Weight (A*L):= h.sober.mult hX; have hu: tile ζ (A*L)=A*L:= EvenCost.forces Y.certified (show Ω ∘ p=Gazebo.raw F d from funext fun v=> (f').smoothed _|>.trans (physics F μ S v)) hc hw ht
 rw [←hu, Cut.tile h.sober.off_bill hX.off_bill,h.ticket,one_mul]
lemma assembledX {A:Mk d}(h:MassCost F (Y.Yield (d:=d)) A): A=T:=by
 have he:= necessary P Y Q hP hq hg μ S H h; rw [← pricing P Y μ S] at he; exact reverse_cancel ( pre_weight P Y μ S ) he
omit H hg hP hq
lemma ζ_tower (h:d≤k): (ζfinal P μ S k).submatrix ( Deck.climb F h ) ( Deck.climb F h )=ζfinal P μ S d:= by
 let g: RG10.Position.Deck F d ↪ RG10.Position.Deck F k:= ⟨_, Deck.climb_inj F h⟩
 have ht:( Zpre P μ S k ).submatrix (g) (g)= Zpre P μ S d:= Z_tied h μ P S Y.certified
 unfold ζfinal; rw [ ← ht ]; exact ( tile_across g (show ∀ v:V,Deck.price F k (g v)=Deck.price F d v from fun v=>rfl) (Zpre P μ S k) ).symm
lemma cost_tower (h:d≤k): (goal P μ S k).submatrix (Deck.climb F h) (Deck.climb F h)=goal P μ S d:=by
 let g: RG10.Position.Deck F d ↪ RG10.Position.Deck F k:= ⟨_,Deck.climb_inj F h⟩
 have ht:( Zpre P μ S k ).submatrix (g) (g)= Zpre P μ S d:= Z_tied h μ P S Y.certified
 apply reverse_cancel (show Weight L from pre_weight P Y μ S)
 rw [ pricing P Y μ S, ←ht ];
 have hx := crossed g (show ∀ v:V,Deck.price F k (g v)=Deck.price F d v from fun v=>rfl) (fun i j ht=> Deck.of_price F h ( ht.trans ( Deck.price_bound F d i ) )) ( Zpre P μ S k ) ( paidZX P Y μ S|>.1.off_bill ); rw [ pricing P Y μ S, show ( ζfinal _ _ _ _ ).submatrix g g= _ from ζ_tower P Y μ S h ] at hx; exact hx.symm
abbrev CheckG {P:Plan F}{W:Drivers}(Y:Patience P W)(Z:∀ i:ℕ,Matrix ( RG10.Position.Deck F i ) ( RG10.Position.Deck F i ) fps)(d:ℕ) : Datum (RG10.Position.Deck F d)→fps:= mix (arrival Y d) (Z d)
include H hq hg hP
include μ
lemma workflow : ∃! Z, Framed P Y Z:= ⟨ goal P μ S, ⟨fun _=> bona P Y Q hP hq hg μ S H, cost_tower P Y μ S⟩, fun Z hz=> funext fun _=> assembledX P Y Q hP hq hg μ S H (hz.born _)⟩ -- struct Framed args check
-- Clean endpoint. mint.f one, one frame, exact weight and barrier. Does not require Shape beyond test.Int.
theorem equality {Z:∀ i:ℕ,Matrix ( RG10.Position.Deck F i ) ( RG10.Position.Deck F i ) fps} (h:Framed P Y Z): CheckG Y Z d=mix ((f').charge ∘ science μ S F d) (ζfinal P μ S d):= by
 unfold CheckG; rw [show arrival Y d=_ from price_Gx P hP hq X μ S hg Y.certified H Y, mix2, necessary P Y Q hP hq hg μ S H (h.born d) ]
end YM.FVAAlt2.Mass
