
# field size
field_count = 39

# census99 fields ordered by code
fields = (
    'C010_GENDER'       , 'C020_AGE'                , 'C031_TAIWANESE'   ,
    'C032_NATIONALITY'  , 'C040_FOREIGN_WORKER'     , 'C050_MARRIAGE'    ,
    'C060_REL_HEAD'     , 'C071_ED_STATUS'          , 'C072_EDUCATION'   ,
    'C073_KINDERGARDEN' , 'C081_6H_CHINESE'         , 'C082_6H_MINNAN'   ,
    'C083_6H_HAKKA'     , 'C084_6H_ABORIGINAL'      , 'C085_6H_OTHER'    ,
    'C091_6P_CHINESE'   , 'C092_6P_MINNAN'          , 'C093_6P_HAKKA'    ,
    'C094_6P_ABORIGINAL', 'C095_6P_OTHER'           , 'C100_5Y_RESIDENCE',
    'C110_MAIN_INCOME'  , 'C121_EMPLOYMENT'         , 'C122_INDUSTRY'    ,
    'C123_OCCUPATION'   , 'C131_WS_STATUS'          , 'C132_WS_LOCATION' ,
    'C141_OFFSPRING'    , 'C142_OFFSPRING_RESIDENCE', 'C151_DIS_EAT'     ,
    'C152_DIS_BED'      , 'C153_DIS_CLOTHES'        , 'C154_DIS_TOILET'  ,
    'C155_DIS_SHOWER'   , 'C156_DIS_OWALK'          , 'C157_DIS_CHORE'   ,
    'C158_DIS_NONE'     , 'C160_ABORIGINAL'         , 'C170_DISABLED')

# ordered by domain size
ordered_fields = [
     ('C010_GENDER', 2), ('C031_TAIWANESE', 2), ('C040_FOREIGN_WORKER', 2),
     ('C081_6H_CHINESE', 2), ('C082_6H_MINNAN', 2), ('C083_6H_HAKKA', 2),
     ('C084_6H_ABORIGINAL', 2), ('C085_6H_OTHER', 2), ('C091_6P_CHINESE', 2),
     ('C092_6P_MINNAN', 2), ('C093_6P_HAKKA', 2), ('C094_6P_ABORIGINAL', 2),
     ('C095_6P_OTHER', 2), ('C151_DIS_EAT', 2), ('C152_DIS_BED', 2),
     ('C153_DIS_CLOTHES', 2), ('C154_DIS_TOILET', 2), ('C155_DIS_SHOWER', 2),
     ('C156_DIS_OWALK', 2), ('C157_DIS_CHORE', 2), ('C158_DIS_NONE', 2),
     ('C073_KINDERGARDEN', 3), ('C110_MAIN_INCOME', 3), ('C121_EMPLOYMENT', 3),
     ('C131_WS_STATUS', 3), ('C160_ABORIGINAL', 3), ('C170_DISABLED', 3),
     ('C132_WS_LOCATION', 4), ('C050_MARRIAGE', 5), ('C071_ED_STATUS', 5),
     ('C142_OFFSPRING_RESIDENCE', 6), ('C141_OFFSPRING', 7), ('C100_5Y_RESIDENCE', 8),
     ('C032_NATIONALITY', 10), ('C072_EDUCATION', 11), ('C060_REL_HEAD', 12),
     ('C020_AGE', 17), ('C123_OCCUPATION', 39), ('C122_INDUSTRY', 80)]

# count distinct on all fields
max_distinct_rows = 1364624
