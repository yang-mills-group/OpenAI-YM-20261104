import YM.RemainderComparison.Encore.Seal
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Encore
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset Solos Lyric Mosaic Serif Marker GridRenewal.Rain
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {L f c : Side} {R:Rep G f}{S:StepData c f}
variable {θ ι:Type} [DecidableEq θ]{J:Marker.Census θ}
variable (M:ι→Lotus.Leaf R)(U:Config G f)(B:Set ι)(l:ι→ℝ)(z:ι→Marker.Poly J)
-- Input log terms REAL * amplitude* and incoming cost.B. Only require uniqueness for occupied logs (fresh padding possible).
def limb(i:ι): Option ℕ:= match (M i).turn with | .logKey _=> none| .gasKey j=>some j

def unitP(i:ι): Marker.Poly J:= Verse.controls B z ({i}:Multiset ι)

def primitive (i:ι) : Marker.Poly J:= ((l i * (M i).ingredient U:ℝ):ℂ) • Verse.controls B z ({i}:Multiset ι)

def Anc (i: ℕ) : Marker.Poly J := ((↑(R.activities.K i U):ℂ)) • 1
local notation "Φ"=> primitive M U B l z
local notation "R₁"=> Anc (J:=J) (R:=R) U
local notation "κ"=> (limb M)
set_option quotPrecheck false
local notation "r"=> R.activities
variable (ζ:Drums M S)
lemma venue (b:ι)(i:ℕ): limb M b=some i↔ (M b).turn= Wing.gasKey i:=by unfold limb; cases (M b).turn <;> simp
lemma plot : unique κ ζ.val :=by
    intro x hx y hy i hp he; apply ζ.prop hx hy; unfold Palette.sign; rw [(venue M x i).1 hp,(venue M y i).1 he]
lemma booths : token κ ζ.val=(team M ζ).gasDue:=by
    ext i; rw [Team.asked,songx]; constructor
    · intro h; obtain ⟨x,hx,h⟩:=h; exact ⟨M x,mem_image.mpr ⟨x,hx,rfl⟩,(venue M x i).mp h⟩
    rintro ⟨a,b,ha⟩; obtain ⟨i,hx,rfl⟩:= mem_image.mp b; exact ⟨i,hx,(venue ..).mpr ha⟩

def doors : Prop:= ∀ i j x, (M i).turn=.logKey x→ (M j).turn=.logKey x→i=j
lemma funded (h:doors M) (u:Finset ι)(hp:unique κ u) : Set.InjOn (Palette.sign M S) u:=by
    intro i hi j hj hz; have he: (M i).turn=(M j).turn:= Team.badged S hz
    cases hx:(M i).turn
    · exact h i j _ hx (he.symm.trans hx)
    exact hp i hi j hj _ ((venue ..).mpr hx) ((venue ..).mpr (he.symm.trans hx))
open Mosaic
local notation "Vʼ"=> Mosaic.raw M ζ
local notation "q"=> Verse.controls B z (Vʼ|>.letters)
lemma tokens (s:Finset ι) : (∏ i∈s,unitP B z i)=Verse.controls B z s.val:=by induction s using Finset.induction_on with
   | empty=> simp [Verse.controls]
   | insert i s hi he=> rw [prod_insert hi,he,Finset.insert_val_of_notMem hi]; simp only [unitP,Verse.controls,Multiset.map_cons,Multiset.map_singleton,Multiset.prod_singleton,Multiset.prod_cons]
lemma labeled : (∏ i∈ ζ.val,primitive M U B l z i)= (↑((Vʼ).stock l * (team M ζ).ingredients U):ℂ) • Verse.controls B z (Vʼ|>.letters):=by
    unfold primitive; rw [Finset.prod_smul]; have he :(∏ i∈ ζ.val,(↑(l i* ((M i).ingredient U)):ℂ))=↑((Vʼ).stock l*(team M ζ).ingredients U):=by rw [←Complex.ofReal_prod,Finset.prod_mul_distrib,Team.ingredients,Solos.shape]; rfl
    rw [he]; exact congr_arg _ (tokens B z ζ.val)
local notation "E" => ((team M ζ))
lemma cares (k:Finset ℕ) :
     (if (r).admissible R.p U k then chop κ Φ R₁ ζ.val k else 0)= (↑((Vʼ).stock l * (team M ζ).bun k U):ℂ) • Verse.controls B z (Vʼ|>.letters):=by
    unfold Team.bun; split; next=>
      unfold chop Team.bill; simp_rw [plot M ζ,true_and, booths M ζ]; split; next=>
         unfold Anc; rw [Finset.prod_smul,prod_const_one,labeled]; rw [smul_mul_smul_comm,mul_one, ← Complex.ofReal_prod,← Complex.ofReal_mul, mul_assoc]; congr!
      next=> simp
    next=> simp
end YM.RemainderComparison.Encore
