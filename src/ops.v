
Class cardinal_of n fset := cardinal_op : fset -> n.
Class compl_of fset := compl_op : fset -> fset.
Class empty_of fset := empty_op : fset.
Class full_of fset := full_op : fset.
Class get_of e fset := get_op : e -> fset -> bool.
Class set_of e fset := set_op : e -> fset -> fset.
Class inter_of fset := inter_op : fset -> fset -> fset.
Class min_of e fset := min_op : fset -> e.
Class remove_of e fset := remove_op : fset -> e -> fset.
Class symdiff_of fset := symdiff_op : fset -> fset -> fset.
Class union_of fset := union_op : fset -> fset -> fset.
Class singleton_of e fset := singleton_op : e -> fset.
Class subset_of fset := subset_op : fset -> fset -> bool.

(* TODO: add notations *)

