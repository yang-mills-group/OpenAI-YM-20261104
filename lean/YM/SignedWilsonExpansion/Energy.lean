import YM.SignedWilsonExpansion.MarkShift
import YangMills.WilsonProof.NativeSupport.YM.FVA2.Press.Deck
import YM.Next.MAXWELL.Flavor
namespace YM.SignedWilsonExpansion.Energy
/-! # Rank-two test port

Extracts the actual `Initialize` w4 port energy before perturbation and traces
its passage as an order-one cubic mark in the high-flow computation. Uses the
plane-wave calculation of FVAMatch/Gyr/Garden (`dancing`,`forecast`) but in
the `portDeck` of this prescription; here no higher ordered derivatives are
needed. No singlet projection. No basis distinguished by measurements. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake
open MS.Garment MS.Motif MS.Halo MS.Motif.Literal MS.Arts Maxwell Maxwell.Free FVA2.Press MS.Theater
open SignedWilsonExpansion HighScale HighRank TreeLine TreeView LocalForm
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{a b c d:Axis}{n:ℕ}
-- plane wave diagnostic
abbrev point0 (i:Axis) : Feet G 0→ₗ[ℝ] G.Color:= { toFun X:= Tensor.diagonal (X.val i) 0,map_add':= fun _ _=> rfl, map_smul':=fun _ _=> rfl }
def sign0 (a b:Axis): Feet G 1 →ₗ[ℝ] G.Color:= point0 b ∘ₗ stepL G Axis 0 a - point0 a ∘ₗ stepL G Axis 0 b
def leg (a b:Axis)(i:Axis)(p:FourP): ℝ:= (if i=b then p a else 0)-(if i=a then p b else 0)
lemma sign0_wave (i:Axis)(p:FourP)(v:G.Color): sign0 a b (speak 1 i p v)= leg a b i p • v:= by
  have hx (j:Axis): point0 j (speak 0 i p v)=if j=i then v else 0:=by
    change (planeC i 0 (fixF p) v).val _ _=_; by_cases he:j=i; · subst j; simp [wearing,Theater.amount]
    rw [Theater.away _ _ _ he]; simp [he]
  rw [sign0,LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.comp_apply,step_at,step_at,map_smul,map_smul,hx,hx]; unfold leg; simp_rw [eq_comm (a:=b) (b:=i),eq_comm (a:=a) (b:=i)]; split_ifs <;> simp [sub_smul]
lemma sign0_nil (F:Head G 2) : sign0 a b (gradS G 1 F)=0:= by
  let P:Submodule ℝ (Head G 2):= LinearMap.ker ((sign0 a b).comp (gradS G 1)); suffices h: ⊤≤P from h (Submodule.mem_top); rw [← termsTop, Submodule.span_le]; rintro F ⟨⟨⟩,k,x,rfl⟩; let q:= Theater.out x; let v:=cl G k; change sign0 a b (gradS G 1 ( speak _ () q v ))=0; rw [grad_at,map_sum]; simp_rw [map_smul,sign0_wave, smul_smul,← Finset.sum_smul]; rw [show (∑ i,q i*(leg a b i q))=0 from ?_,zero_smul]; simp [leg,mul_sub,mul_ite, Finset.sum_sub_distrib]; ring
lemma sign0_curl (F:Feet G 1) : Tensor.diagonal (takeCurl (yard G 0 F) a b) 0=sign0 a b F:= by
  have hv(T:Labels.Taylor G 0): Tensor.diagonal ( takeCurl T a b ) 0=sign0 a b (step_in G 0 T):= by rw [takeCurl_diag]; change _= Tensor.diagonal ((stepL G Axis 0 a (step_in G 0 T)).val b) 0- Tensor.diagonal ((stepL G Axis 0 b (step_in G 0 T)).val a) 0; rw [stepL,stepL, workL,workL]; rfl
  rw [hv,taxiY,carveΩ,map_sub,map_smul,sign0_nil,smul_zero,sub_zero]

def glint (a b:Axis)(k:G.ColorIndex): Witness G 0 where
    toFun X:= ↑(( Tensor.diagonal ( takeCurl X a b ) 0 ) k)
    map_add' X Y:= by rw [show takeCurl (X+Y)=takeCurl X+takeCurl Y from congr_arg Subtype.val (potential.map_add X Y)]; exact Complex.ofReal_add ..
    map_smul' z X:= by rw [show takeCurl (z • X)=z • takeCurl X from congr_arg Subtype.val (potential.map_smul z X)]; exact Complex.ofReal_mul ..
lemma pulse (k:G.ColorIndex): Theater.orbit G (Theater.page 0 (glint a b k))= Motif.F₀ (n:=0) a b k:=by
    rw [Theater.pageX]; funext l; by_cases h:l.length=1; swap; · rw [Motif.rank_α _ _ _ _ (by rw [mod_int]; omega)]; cases l with| nil=>rfl| cons i l=>cases l; exact (h rfl).elim; rfl
    obtain ⟨⟨j,p⟩,rfl⟩:=List.length_eq_one_iff.mp h; rw [ Motif.c_α ]; rcases j with ⟨⟨_|j,_|_⟩,i⟩ <;> ( first | (change (0:ℂ)=_; simp [Motif.at_g]; done )| skip )
    change hitϑ 1 * (↑(( Tensor.diagonal (takeCurl _ a b) 0) k):ℂ)=_
    rw [sign0_curl,sign0_wave]; by_cases hv:i=k <;> by_cases he:j=a <;> by_cases hh:j=b <;>
      simp [cl,leg,Motif.at_g,Motif.spikeV,hv,he,hh,hitϑ,eq_comm] <;> split_ifs <;> simp [mul_sub]

lemma g_area (v : Labels.Taylor G 0) : ∃ Q:Shell G 0, gaugeJet Q=v := by  -- same dimension fact as Pert/Triangle/Operators
  let u := takeCurl v
  have hu : u ∈ onShell G.Color 0 := (show _ ∧ _ from ⟨closedCurl v, fun b w => Finset.sum_eq_zero (fun a _ => ?_)⟩)
  · let Q := (⟨u,hu⟩:Shell G 0); exact ⟨Q,potential.injective (Subtype.ext (match_leg Q))⟩
  unfold grad Tensor.diagonal
  rw [show (fun z:E4=> (u a b) (fun _=>z))=(fun _=>(u a b) 0) from funext (fun x => congrArg _ (funext fun i : Fin 0=>i.elim0))]
  exact congrArg (fun p : E4→L[ℝ] G.Color=> p (basis a)) (congrFun (fderiv_const (E:=E4) (𝕜:=ℝ) (u a b 0)) w)
local notation "µ" => XSpace.On.lifting
abbrev raw (G:Gauge)(a b:Axis):=team G (cell a b) (cell a b)
def off (a b:Axis)(G:Gauge): Labels.Pol G:= ∑ k:G.ColorIndex, Theater.page 0 (glint a b k)*Theater.page 0 (glint a b k)
abbrev plane (a b: Axis)(G:Gauge): Mob G:= fun n=> sume (F₀ (chair n a) (chair n b)) ( F₀ (chair n a) (chair n b) )
lemma sectionE (a b:Axis): µ (raw G a b)=off a b G:= by
    apply Labels.eval_ext; intro X; unfold raw team off; simp_rw [map_sum,map_mul,XSpace.On.lifted, Theater.bookX, bit,symbol_test]; obtain ⟨V,hV⟩:=g_area (X 0); rw [← hV]; simp only [XSpace.On.on_shell]; refine Finset.sum_congr rfl fun k _=>?_ ; have h: glint a b k (gaugeJet V)= ↑(flavor (G:=G) 0 k (cell a b) V):= by unfold glint; simp only [LinearMap.coe_mk, AddHom.coe_mk]; rw [ match_leg ]; rfl
    rw [h]
lemma over_color (a b:Axis): Theater.orbit G (off a b G)=plane a b G 0:= by unfold off plane sume; simp_rw [map_sum,bags,pulse]; rfl

local notation "B" => portDeck G
lemma half (a b:Axis): Theater.At (off a b G) (4,2):= by
  unfold off; refine Submodule.sum_mem _ fun i _=> ?_; exact (show MvPolynomial.IsWeightedHomogeneous _ _ _ from Theater.bypage (glint a b i)).mul (show MvPolynomial.IsWeightedHomogeneous _ _ _ from Theater.bypage (glint a b i)) -- may inferfail
lemma admitted (a b:Axis):off a b G∈Film0 G 4 2 := by
  apply (cinema _).mpr; refine ⟨half a b,?_,?_⟩; rw [← sectionE]; exact (XSpace.On.fits (⟨_,team_label _ _ le_rfl⟩:shellSector G 4)).2
  rw [←sectionE, ← XSpace.On.lift_conj,raw,realTeam]
lemma carryE (a b:Axis): plane a b G 0 ∈ (B).carries 4 2:= by
  rw [← over_color]; let y:Film0 G 4 2 :=⟨_,admitted a b⟩
  rw [show (B).carries 4 2=born G 4 2 from level G 4 2]; refine ⟨ y,?_⟩; have hv: refineF G 4 2 y=y:= by apply Subtype.ext; rw [fixedR]; change µ (reduceEq (off a b G))=off a b G; rw [← sectionE, XSpace.On.lift_recover]
  rw [LinearMap.comp_apply,hv]; rfl
abbrev here (a b:Axis)(G:Gauge):(portDeck G).carries 4 2:= ⟨plane a b G 0,carryE a b⟩
def called (a b:Axis)(G:Gauge)(i:MarkRows.I (portDeck G)):ℝ:= ( Module.finBasis ℝ _ ).repr ( here a b G ) i
lemma found (a b:Axis): MarkRows.ground (called a b G)=plane a b G 0:= by
    have he:= congr_arg (fun p:(B).carries 4 2=>p.val) ( (Module.finBasis ℝ _).sum_repr (here a b G)); simp_rw [AddSubmonoidClass.coe_finsetSum] at he; exact he

abbrev firstE (a b:Axis)(G:Gauge): Mob G:= fun n=> let i:=chair n a; let j:=chair n b; sume (F₀ i j) (quill i j)+ sume (quill i j) (F₀ i j)
abbrev secondE (a b:Axis)(G:Gauge): Mob G:= fun n=> let i:=chair n a; let j:=chair n b; sume (quill i j) (quill i j)
def book (a b:Axis)(G:Gauge): Box (Mob G):=.single 0 (plane a b G)+ .single 1 (firstE a b G)+ .single 2 (secondE a b G)
-- judgment supplies classical Q annihilation on the first homogeneous mark step; no mass premise
open MS.Rock MS.Rock.Path MS.Dock
lemma entry (z:ℂ)(i:ℕ): Literal.value (Mob G) z (book a b G) i=sume (G:=G) (cur z (chair i a) (chair i b)) (cur z (chair i a) (chair i b)):=by
  unfold book; simp only [map_add, value_sl]; simp only [plane,firstE,secondE,sume,Pi.add_apply,pow_zero,one_smul,pow_one,Pi.smul_apply,cur,quill,map_add,map_smul, LinearMap.add_apply,LinearMap.smul_apply,Finset.smul_sum, smul_add,← Finset.sum_add_distrib ]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [smul_smul,pow_two]; abel
lemma book_q : Trill (pulseX G) ( Literal.linear (Mob G) (book a b G) ):= by
  apply Motif.judgment (fun z n=>?_)
  · intro z; ext1 n; change tree parity _ _ _= (0:Rack G n); rw [entry]; refine Mach.tail_shutdown ?_ (Apple.color_r _ _ (Apple.spicy _ _) (Apple.spicy _ _)); let i:=chair n a; let j:=chair n b; have h(t:G.ColorIndex) := Mach.Coven (G:=G) (U:=cur z i j) (Apple.spicy i j) (Cur_sym i j z) (curs z i j) (horr z i j) t; exact Mach.Safe.total _ (fun k _=> Mach.Safe.lipP (h k) (h k))
  rw [entry]; exact Koszul.Symm.sum _ (fun i _=> (Cur_sym _ _ z i).times (Cur_sym _ _ z i))
lemma full : MarkTop.Completion (called a b G) ( firstE a b G 0 ) := by
  constructor
  · apply lease_one.mpr; have hp n:Pace (firstE a b G n) 4 0 3:= ( ( Bay.traceC (Bay.curls (chair n a) (chair n b)) (( Bay.cov _ ).Cartan ( Bay.cov _ )) ) : Pace _ 4 0 3).plus (show Pace _ (2+2) (0+0) ((2:ℤ)+1) from Bay.traceC (( Bay.cov (chair n a) ).Cartan ( Bay.cov (chair n b) )) (Bay.curls _ _))
    refine ⟨Halo.lining hp ?_, Halo.snTag hp, ?_⟩
    · intro n e; let i:=chair n a; let j:=chair n b; have hx: Apple (F₀ i j:Mield G n):= Apple.sub ((Apple.leaf j).runs i) ((Apple.leaf i).runs j); have hv:Apple (quill i j:Mield G n):=(Apple.leaf i).r_eq (Apple.leaf j); dsimp only [firstE]; rw [map_add,Apple.color_r _ _ hx hv, Apple.color_r _ _ hv hx]
    intro w _ h; let i:=chair 0 a; let j:=chair 0 b; have hp: Book.rank 3 (firstE a b G 0):= Rails.add (BulkTop.strictr (rank_α i j) (BulkTop.quill_r i j)) (BulkTop.strictr (BulkTop.quill_r i j) (rank_α i j)); exact hp w (by rw [mod_int]; omega)
  intro w _; have he:= book_q (G:=G) (a:=a) (b:=b) 1 0 w (fun v=>Bool.noConfusion v); unfold BasisC at he; rw [one_smul,Convolve.paired,show antidiagonal 1={(0,1),(1,0)} from by decide,sum_insert (by decide),sum_singleton] at he
  simp only [Motif.χ,map_zero,LinearMap.zero_apply,zero_add, hiss, book,Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne (show (1:ℕ)≠0 from by decide),Finsupp.single_eq_of_ne (show (0:ℕ)≠1 from by decide),Finsupp.single_eq_of_ne (show (1:ℕ)≠2 from by decide),Finsupp.single_eq_of_ne (show (0:ℕ)≠2 from by decide),add_zero] at he; rw [found]; exact eq_neg_of_add_eq_zero_left he

end
end YM.SignedWilsonExpansion.Energy
