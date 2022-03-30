#! python3

import os

substitutions = [
    # The toplevel names in the Prelude
    ("internalCast", "internal_cast"),
    ("F64ToF", "f64_to_f"),
    ("F32ToF", "f32_to_f"),
    ("FToF64", "f_to_f64"),
    ("FToF32", "f_to_f32"),
    ("I64ToI", "i64_to_i"),
    ("I32ToI", "i32_to_i"),
    ("W8ToI", "w8_to_i"),
    ("IToI64", "i_to_i64"),
    ("IToI32", "i_to_i32"),
    ("IToW8", "i_to_w8"),
    ("IToW32", "i_to_w32"),
    ("IToW64", "i_to_w64"),
    ("W32ToW64", "w32_to_w64"),
    ("IToF", "i_to_f"),
    ("I64ToRawPtr", "i64_to_raw_ptr"),  # ?
    ("RawPtrToI64", "raw_ptr_to_i64"),
    ("fromInteger", "from_integer"),
    ("lowWord", "low_word"),
    ("highWord", "high_word"),
    ("getSize", "get_size"),
    ("unsafeFromOrdinal", "unsafe_from_ordinal"),
    ("clampNonnegPrim", "clamp_nonneg_prim"),
    ("scaleVec", "scale_vec"),
    ("BToW8", "b_to_w8"),
    ("W8ToB", "w8_to_b"),
    ("BToI", "b_to_i"),
    ("BToF", "b_to_f"),
    ("OToW8", "o_to_w8"),
    ("isNothing", "is_nothing"),  # ?
    ("isJust", "is_just"),
    ("fstRef", "fst_ref"),
    ("sndRef", "snd_ref"),
    ("runReader", "run_reader"),
    ("withReader", "with_reader"),
    ("runAccum", "run_accum"),
    ("withAccum", "with_accum"),
    ("runState", "run_state"),
    ("withState", "with_state"),
    ("yieldState", "yield_state"),
    ("unsafeIO", "unsafe_io"),  # ?
    ("castPtr", "cast_ptr"),  # ?
    ("storageSize", "storage_size"),
    ("storeTab", "store_table"),
    ("withAlloc", "with_alloc"),
    ("withTabPtr", "with_table_ptr"), # ?
    ("tabFromPtr", "table_from_ptr"), # ?
    ("applyN", "apply_n"),
    ("cumSum", "cumsum"),
    ("derivRev", "deriv_rev"),
    ("checkDerivBase", "check_deriv_base"),
    ("checkDeriv", "check_deriv"),
    ("unsafeCastTable", "unsafe_cast_table"),
    ("toList", "to_list"), # ?
    ("argFilter", "arg_filter"),
    ("appIso", "app_iso"), # ?
    ("flipIso", "flip_iso"), # ?
    ("revIso", "rev_iso"), # ?
    ("idIso", "id_iso"), # ?
    ("getAt", "get_at"),
    ("popAt", "pop_at"),
    ("pushAt", "push_at"),
    ("setAt", "set_at"),
    ("matchWith", "match_with"),
    ("buildWith", "build_with"),
    ("swapPairIso", "swap_pair_iso"), # ?
    ("exceptLens", "except_lens"), # ?
    ("swapEitherIso", "swap_either_iso"), # ?
    ("exceptPrism", "except_prism"),
    ("overLens", "over_lens"),
    ("splitR", "split_r"),
    ("overFields", "over_fields"),
    ("splitV", "split_v"),
    ("sliceFields", "slice_fields"),
    ("withDynamicBuffer", "with_dynamic_buffer"),
    ("maybeIncreaseBufferSize", "maybe_increase_buffer_size"),
    ("addAtIntPtr", "add_at_int_ptr"), # ?
    ("extendDynBuffer", "extend_dynamic_buffer"),
    ("loadDynBuffer", "load_dynamic_buffer"),
    ("pushDynBuffer", "push_dynamic_buffer"),
    ("stringFromCharPtr", "string_from_char_ptr"), # ?
    # Do we want showInt32, showInt64, showFloat32, showFloat64?  They refer
    # to dexrt.cpp
    ("nullRawPtr", "null_raw_ptr"), # ??
    ("fromNullableRawPtr", "from_nullable_raw_ptr"), # ??
    ("cStringPtr", "c_string_ptr"), # ?
    ("withCString", "with_c_string"), # ?
    ("liftState", "lift_state"),
    ("boundedIter", "bounded_iter"),
    ("fromCString", "from_c_string"),
    ("getEnv", "get_env"),
    ("checkEnv", "check_env"),
    ("getOutputStream", "get_output_stream"),
    ("shellOut", "shell_out"),
    ("deleteFile", "delete_file"),
    ("withFile", "with_file"),
    ("writeFile", "write_file"),
    ("readFile", "read_file"),
    ("hasFile", "has_file"),
    ("newTempFile", "new_temp_file"),
    ("withTempFile", "with_temp_file"),
    ("withTempFiles", "with_temp_files"),
    ("fromOrdinal", "from_ordinal"),
    ("castTable", "cast_table"),
    ("threeFry2x32", "threefry_2x32"),
    ("newKey", "new_key"),
    ("splitKey", "split_key"),
    ("randVec", "rand_vec"),
    ("randMat", "rand_mat"),
    ("randInt", "rand_int"),
    ("randnVec", "randn_vec"),
    ("randIdx", "rand_idx"),
    ("searchSorted", "search_sorted"),
    ("minBy", "min_by"),
    ("maxBy", "max_by"),
    ("minimumBy", "minimum_by"),
    ("maximumBy", "maximum_by"),
    ("lexicalOrder", "lexical_order"),
    ("padTo", "pad_to"),
    ("idivCeil", "idiv_ceil"),
    ("isOdd", "is_odd"),
    ("isEven", "is_even"),
    ("isPowerOf2", "is_power_of_2"),
    ("generalIntegerPower", "general_integer_power"),
    ("fromJust", "from_just"), # ?
    ("anySat", "any_sat"),
    ("seqMaybes", "seq_maybes"), # ?
    ("linearSearch", "linear_search"),
    ("listLength", "list_length"),
    ("cumSumLow", "cumsum_low"),
    ("categoricalFromCDF", "categorical_from_cdf"),
    ("normalizePdf", "normalize_pdf"),
    ("cdfForCategorical", "cdf_for_categorical"),
    ("categoricalBatch", "categorical_batch"),
    # diagram.dx
    ("defaultGeomStyle", "default_geom_style"),
    ("concatDiagrams", "concat_diagrams"),
    ("applyTransformation", "apply_transformation"),
    ("flipY", "flip_y"),
    ("moveXY", "move_xy"),
    ("singletonDefault", "singleton_default"),
    ("pointDiagram", "point_diagram"),
    ("updateGeom", "update_geom"),
    ("setFillColor", "set_fill_color"),
    ("setStrokeColor", "set_stroke_color"),
    ("setStrokeWidth", "set_stroke_width"),
    ("removeStroke", "remove_stroke"),
    ("removeFill", "remove_fill"),
    ("strCat", "str_cat"),
    ("strSpaceCatUncurried", "str_space_cat_uncurried"),
    ("selfClosingBrackets", "self_closing_brackets"),
    ("tagBrackets", "tag_brackets"),
    ("tagBracketsAttrUncurried", "tag_brackets_attr_uncurried"),
    ("tagBracketsAttr", "tag_brackets_attr"),
    ("htmlColor", "html_color"),
    ("optionalHtmlColor", "optional_html_color"),
    ("attrString", "attr_string"),
    ("renderGeom", "render_geom"),
    ("computeBounds", "compute_bounds"),
    ("renderSVG", "render_svg"),
    ("renderScaledSVG", "render_scaled_svg"),
    ("moveX", "move_x"),
    ("moveY", "move_y"),
    ("concentricDiagram", "concentric_diagram"),
    # linalg.dx
    ("upperTriDiag", "upper_tri_diag"),
    ("lowerTriDiag", "lower_tri_diag"),
    ("transposeLowerToUpper", "transpose_lower_to_upper"),
    ("lowerTriMat", "lower_tri_mat"),
    ("upperTriMat", "upper_tri_mat"),
    ("swapInPlace", "swap_in_place"),
    ("permToTable", "perm_to_table"),
    ("permSign", "perm_sign"),
    # parser.dx
    ("fromOrdinalExc", "from_ordinal_exc"),
    ("indexList", "index_list"),
    ("runParserPartial", "run_parser_partial"),
    ("pChar", "p_char"),
    ("pEOF", "p_eof"),
    ("runParser", "run_parser"),
    ("parseAny", "parse_any"),
    ("parseDigit", "parse_digit"),
    ("parseMany", "parse_many"),
    ("parseUnsignedInt", "parse_unsigned_int"),
    ("parseInt", "parse_int"),
    # plot.dx
    ("applyScale", "apply_scale"),
    ("unitTypeScale", "unit_type_scale"),
    ("projectUnitInterval", "project_unit_interval"),
    ("unitIntervalScale", "unit_interval_scale"),
    ("mapScale", "map_scale"),
    ("floatScale", "float_scale"),
    ("getScaled", "get_scaled"),
    ("lowColor", "low_color"),
    ("highColor", "high_color"),
    ("makeRGBColor", "make_rgb_color"),
    ("colorScale", "color_scale"),
    ("plotToDiagram", "plot_to_diagram"),
    ("showPlot", "show_plot"),
    ("blankData", "blank_data"),
    ("blankPlot", "blank_plot"),
    ("autoScale", "auto_scale"),
    ("setXData", "set_x_data"),
    ("setYData", "set_y_data"),
    ("setCData", "set_c_data"),
    ("xyPlot", "xy_plot"),
    ("xycPlot", "xyc_plot"),
    ("yPlot", "y_plot"),
    # png.dx
    ("encodingTable", "encoding_table"),
    ("decodingTable", "decoding_table"),
    ("getChunks", "get_chunks"),
    ("base64sToBytes", "base64s_to_bytes"),
    ("bytesToBase64s", "bytes_to_base64s"),
    ("base64ToAscii", "base64_to_ascii"),
    ("encodeChunk", "encode_chunk"),
    ("base64Encode", "base64_encode"),
    ("asciiToBase64", "ascii_to_base64"),
    ("decodeChunk", "decode_chunk"),
    ("base64Decode", "base64_decode"),
    ("makePNG", "make_png"),
    ("pngsToGif", "pngs_to_gif"),
    ("imgToHtml", "img_to_html"),
    ("floatTo8Bit", "float_to_8bit"),
    ("imgToPng", "img_to_png"),
    # set.dx
    ("allExceptLast", "all_except_last"),
    ("mergeUniqueSortedLists", "merge_unique_sorted_lists"),
    ("removeDuplicatesFromSorted", "remove_duplicates_from_sorted"),
    ("toSet", "to_set"), # ?
    ("setSize", "set_size"),
    ("setUnion", "set_union"),
    ("setIntersect", "set_intersect"),
    ("stringToSetIx", "string_to_set_ix"),
    ("setIxToString", "set_ix_to_string"),
    # sort.dx
    ("concatTable", "concat_table"),
    ("mergeSortedTables", "merge_sorted_tables"),
    ("mergeSortedLists", "merge_sorted_lists"),
    ("isSorted", "is_sorted"),
]

def do(cmd):
  print(cmd)
  os.system(cmd)

msgs = []

def do_git(msg):
  if False:
    do(f'git ci -a -m "{msg}"')
  else:
    msgs.append(msg)

def subst_sed(old, new):
  code1 = os.waitstatus_to_exitcode(
    os.system(f'find . -name "*.dx" | grep -v .stack-work | xargs grep -E "[a-zA-Z0-9_%\\\"]{old}"'))
  code2 = os.waitstatus_to_exitcode(
    os.system(f'find . -name "*.dx" | grep -v .stack-work | xargs grep -E "{old}[a-zA-Z0-9_%\\\"]"'))
  code3 = os.waitstatus_to_exitcode(
    os.system(f'find . -name "*.dx" | grep -v .stack-work | xargs grep -E "([^a-zA-Z0-9_%\\\"]|$){new}"'))
  if (code1 > 0 and code2 > 0 and code3 > 0):  # Last grep in each pipe found nothing
    do(f'find . -name "*.dx" | grep -v .stack-work | xargs sed -i -e \'s/{old}/{new}/g\'')
    do_git(f'Convert {old} to {new}.')
  else:
    print(f"Not substituting {old} mechanically (see grep output above)")

def subst_dex(old, new):
  do(f'find . -name "*.dx" | grep -v .stack-work | xargs stack exec dex -- --lib-path lib rename {old} {new}')
  if old == "fromInteger":
    do('sed -i -e \'s/"fromInteger"/"from_integer"/\' src/lib/Inference.hs')
  if old == "applyN":
    do('sed -i -e \'s/### ApplyN/### apply_n/\' lib/prelude.dx')
  if old == "toList":
    do('sed -i -e \'s/"toList"/"to_list"/\' src/lib/Parser.hs')
  do_git(f'Convert {old} to {new}.')

for (old, new) in substitutions:
  if old in ['toList', 'unsafeCastTable',
             'unsafeFromOrdinal', 'IToF', 'I64ToI']:
    do(f'find python/ -name "*.py" | xargs sed -i -e \'s/{old}/{new}/g\'')
  if old == "concentricDiagram":
    subst_sed(old, new)
  else:
    subst_dex(old, new)

if msgs:
  msg = "Rename toplevel names in the Dex corpus to snake_case\n\n" + "\n".join(msgs)
  do(f'git ci -a -m "{msg}"')
