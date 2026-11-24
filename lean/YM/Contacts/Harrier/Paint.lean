import YM.Contacts.Harrier.Band
import YM.Contacts.Harrier.Cymbal
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
namespace Transfer
open Parcel Prairie Planned.PrimaryIntegral295
variable {e:Parcel G} {p:Word}{s:Parcel.Step}{S:Boom} (T:e.License S ζ)(hp:OK S p)(hs:s∈S)
open Cartons Pierian Font MultiNext.SignedSource Pattern Tensor Place Carrier Barrage Barrage.Reserve.Oasis
local notation "Γ" => terrain ζ (Dye G)
-- leading observation formula, for whichever rank marks first. Preview tensor-base h. Used to determine triangular part of continuation at all orders.
variable {H: Labels.Frame G h} (u:Badge H){x:Dye G}{V: Sketch G}
def shade (e:Parcel G)(p:Word)(s:Parcel.Step)(v:Site s.L)(K:Field (Fin k) (Node (Dye G))) := printRun (Trace.wreath (curb s v) (install (Origin.bleed G (e.gas p s))) K)
include T hs hp
variable {K:ℕ}(hT:Demand S e M K)(hi:i≤K) (hu:u.slot ≤ M)(hv:Living x M D V ζ)
include hT hi hv
lemma vanguard (v:Site s.L)(he:r≤M+i)(hZ:Harrier.Before Γ D x V i r 0) : sail (pass e p s M v V) i r=fun φ=> shade e p s v (sail V i r (desk s v φ)):= by
    apply sub_eq_zero.mp; obtain ⟨c,hc,B⟩:= (passport (v:=v) T hs x (D:=D) hT _ hi _ he).1; obtain ⟨b,hb,Y⟩:= keep_est (k:=0) (D:=D) T hs v x he; let F:= motion e p s v i r V; let Z:= lead e p s v i r V; let W:= sail (pass e p s M v V) i r; have hf: W-Z=0:= w_hole (mul_zero c ▸ (B V hv 0 le_rfl hZ).1 _ hp); let R:= keep e p s v M i r V; change W-F=0; rw [sub_eq_zero.mp hf,show Z=F-R from primogen T hp hs v he hv,show R=0 from w_hole (mul_zero b ▸ Y V 0 le_rfl hZ p),sub_zero,sub_self]
include hu
lemma vital (v:Site s.L) (hh:Harrier.Before Γ D x V i u.slot 0) : u.key (pass e p s M v V) M i = (cursor H u.pull u.slot (shade e p s v (V (desk s v u.phi) i u.slot)) u.loc).re:= by
    let t:=(2*ζ); let h:= received T hp hs (v:=v) hv; obtain ⟨a,ha,A⟩:= u.head_price (ζ:=2*ζ) (i:=i) (D:=D) (lt_of_lt_of_le T.light T.down) hu x; obtain ⟨b,hb,P⟩:= prior_passed T hs x (D:=D) (r:=u.slot) hT hi v; have hu' : u.slot ≤ M + i:= hu.trans (Nat.le_add_right ..); rw [show _=cursor H u.pull u.slot (sail _ i u.slot u.phi) u.loc from congr_arg (fun Q=>cursor H u.pull u.slot Q u.loc) (congr_fun (vanguard T hp hs hT hi hv v hu' hh) u.phi).symm]; exact sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [mul_zero] using A _ h (b*0) (by rw [mul_zero]) (P p hp V hv 0 le_rfl hh))) -- u arg order
omit hT hi hu hv
private lemma shade_budget (v:Site s.L)(hx:Rest Γ (0,x) K' b): ∃ C,Rest Γ (0,x) (shade (k:=k) e p s v K') C:= by
    rw [shade,Lotus.orchid]; let W:= Origin.bleed_strip (G:=G) (s:=ζ) (strip_mono (stiff e p s) (by have ht:=T.warm; push_cast at ht; linarith only [ht,NNReal.coe_nonneg ζ]) le_rfl) e.tax_pos.le; exact ⟨_,Hinges.hoist_price x W e.tax_pos.le (le_trans (div_le_div_of_nonneg_right (a:=(ζ:ℝ)) (NNReal.coe_le_coe.mpr T.down) (side_pos _).le) (Parcel.step_reserved s ζ)) (Lotus.staple (curb s v) hx)⟩
lemma lamps (v:Site s.L) {X:Field (Fin k) (Node (Dye G))}(b:ℝ)(hx:Rest Γ (0,x) X b)(hP:Poem X)(hh:u.pull ≤ e.J)(hs':∀ j<u.pull,Remains j X): cursor H u.pull k (shade e p s v X)=cursor H u.pull k (unitStep s.L ^ u.pull • X):= by
    let R:= shade e p s v X; let a:=unitStep s.L ^ u.pull; obtain ⟨d,D⟩:= shade_budget T hp hs v hx; let Y:=a • X; apply sub_eq_zero.mp; rw [← curs_sub H D (hx.smul a) T.light T.light (print_even _) (hP.scale _)]; exact skims H (by show Poem (R-Y); rw [sub_eq_add_neg]; exact (print_even _).add (hP.scale a).minus) (D.sub (hx.smul _)) T.light (H.bound _) (band_same T.light hx hs' T hs hP hh _)
omit hs hp T
lemma value_axis (v: H.Index) {X:bore G}(he:Based ζ x M X)(hp:0<ζ)(hu:(H.grades v).2≤ M): fill H M X 0 v = (cursor H (H.grades v).1 (H.grades v).2 (X 0 (H.grades v).2) v).re:= by
    let k:= (H.grades v).2; let R:= X 0 k; let p:= coil X M (M+4+0-k); obtain ⟨hc,B,hB⟩:= he; let H':= coil_tags hc hB hp (M+4+0-k); have hP(d:ℕ)(he:d<k) : p d=0:= by unfold p coil dazzle shiftA; split_ifs <;> first| rfl | (unfold Catch.cap at *; omega)
    let U:=h*(h+1); have hk : tower p h k=subcode (d:=h) (Shuttle.sheet k R (Tide.lens G U)):= by
       funext i; refine Fin.lastCases ?_ (fun i=>?_) i; swap
       · unfold subcode tower; rw [Pi.single_eq_of_ne (Fin.castSucc_ne_last _),hP i.castSucc.val i.isLt]; have hh(y:Fin i.val→ Node (Dye G)): blanket (i:ℕ) 0 (Tide.lens G U) y=0:= by ext; simp [blanket]
         change (∑' y, blanket i.val 0 (Tide.lens G U) y)=0; simp [hh]
       unfold subcode Cartons.tower; rw [Pi.single_eq_same]; exact congr_arg (fun Q=> Shuttle.sheet k Q _) (Pocket.current_coil M X hu) -- he wrong M+0
    have ht' : cursor H (H.grades v).1 k R v= ((velum H p v:ℝ):ℂ):= by unfold cursor; rw [←hk]; exact cane H' v
    unfold fill; rw [if_pos (by omega)]; exact (congr_arg Complex.re ht').symm
end Transfer
end
end YM.Contacts.Harrier
