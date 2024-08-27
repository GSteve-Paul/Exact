if (CoinUtils_INCLUDE_DIR AND CoinUtils_LIBRARIES)
    set(CoinUtils_FIND_QUIETLY TRUE)
endif ()

find_path(CoinUtils_INCLUDE_DIR NAMES coin/CoinMpsIO.hpp coin/CoinLpIO.hpp)
find_library(CoinUtils_LIBRARIES NAMES CoinUtils libCoinUtils)
MESSAGE(STATUS "CoinUtils libs: " ${CoinUtils_LIBRARIES})
